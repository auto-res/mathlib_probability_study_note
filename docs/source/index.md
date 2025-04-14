Mathlib probability study note documentation
============================================

このドキュメントはMathlib4の[確率論](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability)と[測度論](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/MeasureTheory)の内容を理解するための勉強ノートです. 基礎的な部分(特に定義)を理解することを目標にします. 目次の順番は依存関係を意識しています. 今後の予定については[こちら](plan.md).

このノートブックへの貢献を歓迎しています. お気軽にPull RequestやIssueをお寄せください.

## Filter
[Filter.Defs](Filter/Defs.md) - フィルタに関する概念  
[Filter.Basic](Filter/Basic.md) - フィルタの基本的な性質  

## MeasureTheory

### Outer Measure

[MeasureTheory.OuterMeasure.Defs](MeasureTheory/OuterMeasure/Defs.md) - 外測度の定義  
[MeasureTheory.OuterMeasure.AE](MeasureTheory/OuterMeasure/AE.md) - Almost everywhereの定義  
[MeasureTheory.OuterMeasure.OfFunction](MeasureTheory/OuterMeasure/OfFunction.md) - 外測度の別定義  
[MeasureTheory.OuterMeasure.Induced](MeasureTheory/OuterMeasure/Induced.md) - 外測度の可測集合への制限  

### MeasurableSpace

[MeasureTheory.MeasurableSpace.Defs](MeasureTheory/MeasurableSpace/Defs.md) - 可測空間, 可測関数の定義  
[MeasureTheory.MeasurableSpace.Basic](MeasureTheory/MeasurableSpace/Basic.md) - 可測空間の基本的な性質  
### Measure

[MeasureTheory.Measure.MeasureSpaceDef](MeasureTheory/Measure/MeasureSpaceDef.md) - 測度の定義  

### Function

[MeasureTheory.Function.SimpleFunc](MeasureTheory/Function/SimpleFunc.md) - 単関数の定義  
[MeasureTheory.Function.Lebesgue](MeasureTheory/Measure/Lebesgue.md) - lintegral   
[MeasureTheory.Function.HasFiniteIntegral](MeasureTheory/Function/HasFiniteIntegral.md) - 絶対可積分性の定義  
[MeasureTheory.Function.Integrable](MeasureTheory/Function/Integrable.md) - 可積分性の定義

## ProbabilityTheory