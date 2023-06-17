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
package org.apache.calcite.rel.metadata;

import org.apache.calcite.plan.RelOptTable;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelReferentialConstraint;
import org.apache.calcite.rel.SingleRel;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.Calc;
import org.apache.calcite.rel.core.Correlate;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Intersect;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.Minus;
import org.apache.calcite.rel.core.Project;
import org.apache.calcite.rel.core.Sort;
import org.apache.calcite.rel.core.TableModify;
import org.apache.calcite.rel.core.TableScan;
import org.apache.calcite.rel.core.Union;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexProgram;
import org.apache.calcite.util.ImmutableBitSet;
import org.apache.calcite.util.Util;

import com.google.common.collect.ImmutableListMultimap;
import com.google.common.collect.Maps;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * RelMdForeignKeys supplies a default implementation of
 * {@link RelMetadataQuery#getForeignKeys} for the standard logical algebra.
 * The relNodes supported are same to {@link RelMetadataQuery#getUniqueKeys(RelNode)}
 */
public class RelMdForeignKeys
    implements MetadataHandler<BuiltInMetadata.ForeignKeys> {
  public static final ImmutableBitSet EMPTY_BIT_SET = ImmutableBitSet.of();
  public static final RelMetadataProvider SOURCE =
      ReflectiveRelMetadataProvider.reflectiveSource(
          new RelMdForeignKeys(), BuiltInMetadata.ForeignKeys.Handler.class);

//~ Constructors -----------------------------------------------------------

  private RelMdForeignKeys() {}

//~ Methods ----------------------------------------------------------------

  @Override public MetadataDef<BuiltInMetadata.ForeignKeys> getDef() {
    return BuiltInMetadata.ForeignKeys.DEF;
  }

  public ImmutableBitSet getForeignKeys(Filter rel, RelMetadataQuery mq, boolean containNulls) {
    return mq.getForeignKeys(rel.getInput(), containNulls);
  }

  public ImmutableBitSet getForeignKeys(Sort rel, RelMetadataQuery mq, boolean containNulls) {
    return mq.getForeignKeys(rel.getInput(), containNulls);
  }

  public ImmutableBitSet getForeignKeys(Correlate rel, RelMetadataQuery mq,
      boolean containNulls) {
    return mq.getForeignKeys(rel.getLeft(), containNulls);
  }

  public ImmutableBitSet getForeignKeys(TableModify rel, RelMetadataQuery mq,
      boolean containNulls) {
    return mq.getForeignKeys(rel.getInput(), containNulls);
  }

  public ImmutableBitSet getForeignKeys(Join rel, RelMetadataQuery mq, boolean containNulls) {
    final RelNode left = rel.getLeft();
    final RelNode right = rel.getRight();
    if (!rel.getJoinType().projectsRight()) {
      // only return the foreign keys from the LHS since a semi or anti join only
      // returns the LHS
      return mq.getForeignKeys(left, containNulls);
    }

    int nLeftColumns = rel.getLeft().getRowType().getFieldList().size();
    ImmutableBitSet outForeignKeys = ImmutableBitSet.of();

    if (!rel.getJoinType().generatesNullsOnLeft() || containNulls) {
      ImmutableBitSet leftInputForeignKeys = mq.getForeignKeys(left, containNulls);
      outForeignKeys = outForeignKeys.union(leftInputForeignKeys);
    }
    if (!rel.getJoinType().generatesNullsOnRight() || containNulls) {
      ImmutableBitSet rightInputForeignKeys = mq.getForeignKeys(right, containNulls);
      ImmutableBitSet.Builder rightOutForeignKeys = ImmutableBitSet.builder();
      for (int index : rightInputForeignKeys.asList()) {
        rightOutForeignKeys.set(index + nLeftColumns);
      }
      outForeignKeys = outForeignKeys.union(rightOutForeignKeys.build());
    }
    return outForeignKeys;
  }

  public ImmutableBitSet getForeignKeys(Aggregate rel, RelMetadataQuery mq,
      boolean containNulls) {
    final ImmutableBitSet groupSet = rel.getGroupSet();
    if (groupSet.isEmpty()) {
      return EMPTY_BIT_SET;
    }
    final ImmutableBitSet inputForeignKeys = mq.getForeignKeys(rel.getInput(), containNulls);
    if (inputForeignKeys.isEmpty()) {
      return EMPTY_BIT_SET;
    }
    return groupSet.intersect(inputForeignKeys);
  }

  public ImmutableBitSet getForeignKeys(Project rel, RelMetadataQuery mq,
      boolean containNulls) {
    return getProjectForeignKeys(rel, mq, containNulls, rel.getProjects());
  }

  public ImmutableBitSet getForeignKeys(Calc rel, RelMetadataQuery mq,
      boolean containNulls) {
    RexProgram program = rel.getProgram();
    return getProjectForeignKeys(rel, mq, containNulls,
        Util.transform(program.getProjectList(), program::expandLocalRef));
  }

  private static ImmutableBitSet getProjectForeignKeys(SingleRel rel, RelMetadataQuery mq,
      boolean containNulls,
      List<RexNode> projExprs) {

    // Single input can be mapped to multiple outputs
    final ImmutableListMultimap.Builder<Integer, Integer> inToOutIndexBuilder =
        ImmutableListMultimap.builder();
    final ImmutableBitSet.Builder inColumnsBuilder = ImmutableBitSet.builder();
    for (int i = 0; i < projExprs.size(); i++) {
      RexNode projExpr = projExprs.get(i);
      if (projExpr instanceof RexInputRef) {
        int inputIndex = ((RexInputRef) projExpr).getIndex();
        inToOutIndexBuilder.put(inputIndex, i);
        inColumnsBuilder.set(inputIndex);
      }
    }
    final ImmutableBitSet inColumnsUsed = inColumnsBuilder.build();
    if (inColumnsUsed.isEmpty()) {
      return EMPTY_BIT_SET;
    }

    final Map<Integer, ImmutableBitSet> mapInToOutPos =
        Maps.transformValues(inToOutIndexBuilder.build().asMap(), ImmutableBitSet::of);
    final ImmutableBitSet inputForeignKeys =
        mq.getForeignKeys(rel.getInput(), containNulls);
    if (inputForeignKeys.isEmpty()) {
      return EMPTY_BIT_SET;
    }

    ImmutableBitSet allOutColumns = ImmutableBitSet.of();
    for (int index : inputForeignKeys.asList()) {
      ImmutableBitSet outColumns = mapInToOutPos.get(index);
      if (outColumns != null && !outColumns.isEmpty()) {
        allOutColumns = allOutColumns.union(outColumns);
      }
    }
    return allOutColumns;
  }

  public ImmutableBitSet getForeignKeys(TableScan rel, RelMetadataQuery mq,
      boolean containNulls) {
    final RelOptTable table = rel.getTable();
    final BuiltInMetadata.ForeignKeys.Handler handler =
        table.unwrap(BuiltInMetadata.ForeignKeys.Handler.class);
    if (handler != null) {
      return handler.getForeignKeys(rel, mq, containNulls);
    }

    final List<RelReferentialConstraint> referentialConstraints =
        table.getReferentialConstraints();
    if (referentialConstraints == null || referentialConstraints.isEmpty()) {
      return EMPTY_BIT_SET;
    }
    Set<Integer> foreignKeys = referentialConstraints.stream()
        .map(RelReferentialConstraint::getColumnPairs)
        .flatMap(Collection::stream)
        .map(pair -> {
          return pair.source;
        })
        .collect(Collectors.toSet());

    if (!containNulls) {
      final List<RelDataTypeField> fieldList = rel.getRowType().getFieldList();
      foreignKeys = foreignKeys.stream()
          .filter(index -> !fieldList.get(index).getType().isNullable())
          .collect(Collectors.toSet());
    }
    return ImmutableBitSet.of(foreignKeys);
  }

  /**
   * The foreign keys of Union are precisely the intersection of its every
   * input foreign keys.
   */
  public ImmutableBitSet getForeignKeys(Union rel, RelMetadataQuery mq,
      boolean containNulls) {

    ImmutableBitSet foreignKeys = ImmutableBitSet.of();
    for (RelNode input : rel.getInputs()) {
      ImmutableBitSet inputForeignKeys = mq.getForeignKeys(input, containNulls);
      if (inputForeignKeys.isEmpty()) {
        return EMPTY_BIT_SET;
      }
      foreignKeys = foreignKeys.isEmpty()
          ? inputForeignKeys : foreignKeys.intersect(inputForeignKeys);
    }
    return foreignKeys;
  }

  /**
   * The foreign keys of Intersect are precisely the union set of its every
   * input foreign keys.
   */
  public ImmutableBitSet getForeignKeys(Intersect rel, RelMetadataQuery mq,
      boolean containNulls) {

    ImmutableBitSet foreignKeys = ImmutableBitSet.of();
    for (RelNode input : rel.getInputs()) {
      ImmutableBitSet inputForeignKeys = mq.getForeignKeys(input, containNulls);
      if (inputForeignKeys.isEmpty()) {
        continue;
      }
      foreignKeys = foreignKeys.union(inputForeignKeys);
    }
    return foreignKeys;
  }

  /**
   * The foreign keys of Minus are precisely the foreign keys of its first input.
   */
  public ImmutableBitSet getForeignKeys(Minus rel, RelMetadataQuery mq,
      boolean containNulls) {
    return mq.getForeignKeys(rel.getInput(0), containNulls);
  }

  /** Catch-all rule when none of the others apply. */
  public ImmutableBitSet getForeignKeys(RelNode rel, RelMetadataQuery mq,
      boolean containNulls) {
    // no information available
    return EMPTY_BIT_SET;
  }
}
