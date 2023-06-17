/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.rel.rules;

import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.RelRule;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelReferentialConstraint;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.JoinInfo;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.logical.LogicalJoin;
import org.apache.calcite.rel.logical.LogicalProject;
import org.apache.calcite.rel.metadata.RelColumnOrigin;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexUtil;
import org.apache.calcite.tools.RelBuilderFactory;
import org.apache.calcite.util.ImmutableBitSet;
import org.apache.calcite.util.mapping.IntPair;

import org.immutables.value.Value;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.BooleanSupplier;
import java.util.stream.Collectors;

/**
 * Planner rule that matches an {@link Project}
 * on a {@link Join} and removes the join provided that the join is a left or
 * right join and the join keys are unique, and removes the join provided that
 * the join is inner join and the join keys are foreign and unique key,
 * and the foreign key is not nullable.
 *
 * <p>For instance,
 *
 * <blockquote>
 * <pre>select s.product_id
 * from sales as s
 * left join product as p
 * on s.product_id = p.product_id</pre></blockquote>
 *
 * <p>becomes
 *
 * <blockquote>
 * <pre>select s.product_id from sales as s</pre></blockquote>
 *
 * <p>Another instance,
 *
 * <blockquote>
 * <pre>select e.deptno, e.ename
 * from emp as e
 * inner join dept as d
 * on e.deptno = d.deptno</pre></blockquote>
 *
 * <p>becomes
 *
 * <blockquote>
 * <pre>select e.deptno, e.ename from emp as e</pre></blockquote>
 */
@Value.Enclosing
public class ProjectJoinRemoveRule
    extends RelRule<ProjectJoinRemoveRule.Config>
    implements SubstitutionRule {

  /** Creates a ProjectJoinRemoveRule. */
  protected ProjectJoinRemoveRule(Config config) {
    super(config);
  }

  @Deprecated // to be removed before 2.0
  public ProjectJoinRemoveRule(
      Class<? extends Project> projectClass,
      Class<? extends Join> joinClass, RelBuilderFactory relBuilderFactory) {
    this(Config.DEFAULT.withRelBuilderFactory(relBuilderFactory)
        .as(Config.class)
        .withOperandFor(projectClass, joinClass));
  }

  @Override public void onMatch(RelOptRuleCall call) {
    final Project project = call.rel(0);
    final Join join = call.rel(1);
    final boolean isLeftJoin = join.getJoinType() == JoinRelType.LEFT;
    final boolean isRightJoin = join.getJoinType() == JoinRelType.RIGHT;
    final boolean isInnerJoin = join.getJoinType() == JoinRelType.INNER;

    // Check project range
    ImmutableBitSet projectBits = RelOptUtil.InputFinder.bits(project.getProjects(), null);
    final int leftFieldsNum = join.getLeft().getRowType().getFieldCount();
    final boolean onlyUseLeft = projectBits.asList().stream()
        .allMatch(i -> i >= 0 && i < leftFieldsNum);
    final boolean onlyUseRight = projectBits.asList().stream().allMatch(i -> i >= leftFieldsNum
            && i < join.getRowType().getFieldCount());

    if (!onlyUseLeft && !onlyUseRight) {
      return;
    }
    if (isLeftJoin && !onlyUseLeft) {
      return;
    }
    if (isRightJoin && !onlyUseRight) {
      return;
    }

    JoinInfo joinInfo = join.analyzeCondition();
    final List<Integer> leftKeys = joinInfo.leftKeys;
    final List<Integer> rightKeys = joinInfo.rightKeys;
    final RelMetadataQuery mq = call.getMetadataQuery();

    // For inner join, should also check foreign keys additionally
    if (JoinRelType.INNER == join.getJoinType()) {
      final ImmutableBitSet leftForeignKeys = mq.getForeignKeys(join.getLeft(), false);
      final ImmutableBitSet rightForeignKeys = mq.getForeignKeys(join.getRight(), false);
      if (onlyUseLeft && !areForeignKeysValid(
          leftKeys, rightKeys, leftForeignKeys, mq, join.getLeft(), join.getRight())) {
        return;
      }
      if (onlyUseRight && !areForeignKeysValid(
          rightKeys, leftKeys, rightForeignKeys, mq, join.getRight(), join.getLeft())) {
        return;
      }
    }

    BooleanSupplier isLeftSideReserved = () -> isLeftJoin || (isInnerJoin && onlyUseLeft);
    final List<Integer> joinKeys = isLeftSideReserved.getAsBoolean() ? rightKeys : leftKeys;
    if (Boolean.FALSE.equals(
        mq.areColumnsUnique(isLeftSideReserved.getAsBoolean() ? join.getRight() : join.getLeft(),
            ImmutableBitSet.of(joinKeys)))) {
      return;
    }

    RelNode node;
    if (isLeftSideReserved.getAsBoolean()) {
      node =
          project.copy(project.getTraitSet(), join.getLeft(),
              project.getProjects(), project.getRowType());
    } else {
      final List<RexNode> newExprs = project.getProjects().stream()
          .map(expr -> RexUtil.shift(expr, -leftFieldsNum))
          .collect(Collectors.toList());
      node =
          project.copy(project.getTraitSet(), join.getRight(), newExprs,
              project.getRowType());
    }
    call.transformTo(node);
  }

  /**
   * Check as following:
   * 1. Make sure that every foreign column is always a foreign key.
   * 2. The target of foreign key is the correct corresponding unique key.
   */
  private static boolean areForeignKeysValid(List<Integer> foreignColumns,
      List<Integer> uniqueColumns, ImmutableBitSet foreignKeys, RelMetadataQuery mq,
      RelNode foreignSideRel, RelNode uniqueSideRel) {
    if (foreignKeys.isEmpty()) {
      return false;
    }
    if (!foreignKeys.contains(ImmutableBitSet.of(foreignColumns))) {
      return false;
    }
    List<RelReferentialConstraint> referentialConstraints;
    for (IntPair foreignUniqueKey : IntPair.zip(foreignColumns, uniqueColumns)) {
      RelColumnOrigin foreignOrigin = mq.getColumnOrigin(foreignSideRel, foreignUniqueKey.source);
      RelColumnOrigin uniqueOrigin = mq.getColumnOrigin(uniqueSideRel, foreignUniqueKey.target);
      if (foreignOrigin == null || uniqueOrigin == null) {
        return false;
      }
      referentialConstraints = foreignOrigin.getOriginTable().getReferentialConstraints();
      if (referentialConstraints == null || referentialConstraints.isEmpty()) {
        return false;
      }

      final Set<IntPair> constraintsSet = referentialConstraints.stream()
          .map(RelReferentialConstraint::getColumnPairs)
          .flatMap(Collection::stream)
          .collect(Collectors.toSet());
      if (!constraintsSet.contains(
          IntPair.of(
          foreignOrigin.getOriginColumnOrdinal(),
          uniqueOrigin.getOriginColumnOrdinal()))) {
        return false;
      }
    }
    return true;
  }

  /** Rule configuration. */
  @Value.Immutable
  public interface Config extends RelRule.Config {
    Config DEFAULT = ImmutableProjectJoinRemoveRule.Config.of()
        .withOperandFor(LogicalProject.class, LogicalJoin.class);

    @Override default ProjectJoinRemoveRule toRule() {
      return new ProjectJoinRemoveRule(this);
    }

    /** Defines an operand tree for the given classes. */
    default Config withOperandFor(Class<? extends Project> projectClass,
        Class<? extends Join> joinClass) {
      return withOperandSupplier(b0 ->
          b0.operand(projectClass).oneInput(b1 ->
              b1.operand(joinClass).predicate(join ->
                  join.getJoinType() == JoinRelType.LEFT
                      || join.getJoinType() == JoinRelType.RIGHT
                      || join.getJoinType() == JoinRelType.INNER).anyInputs()))
          .as(Config.class);
    }
  }
}
