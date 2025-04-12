Mathlib probability study note documentation
============================================

このドキュメントはMathlib4の[確率論](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability)と[測度論](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/MeasureTheory)の内容を理解するための勉強ノートです. 基礎的な部分(特に定義)を理解することを目標にします. 目次の順番は依存関係を意識しています. 今後の予定については[こちら](plan.md).

どなたでも編集や投稿を歓迎します.
特にfilter_upwardとvolume_tacの説明をしてくださる方を探しています.

## Filter
[Filter.Defs, Basic](Filter/Defs_Basic.md) - フィルタ, Eventuallyの定義, filter_upwards (4/12)

## MeasureTheory

### Outer Measure

[MeasureTheory.OuterMeasure.Defs](MeasureTheory/OuterMeasure/Defs.md) - 外測度の定義 (4/7)  
[MeasureTheory.OuterMeasure.AE](MeasureTheory/OuterMeasure/AE.md) - Almost everywhereの定義 (4/8)
[MeasureTheory.OuterMeasure.OfFunction](MeasureTheory/OuterMeasure/OfFunction.md) - 外測度の別定義 (4/12)
[MeasureTheory.OuterMeasure.Induced](MeasureTheory/OuterMeasure/Induced.md) - 外測度の$\sigma$-加法族への制限 (4/12)

### MeasurableSpace

[MeasureTheory.MeasurableSpace.Defs](MeasureTheory/MeasurableSpace/Defs.md) - 可測空間, 可測関数の定義 (4/9)  
[MeasureTheory.MeasurableSpace.Basic](MeasureTheory/MeasurableSpace/Basic.md) - 可測空間の基本的な性質 (4/12)

### Measure

[MeasureTheory.Measure.MeasureSpaceDef](MeasureTheory/Measure/MeasureSpaceDef.md) - 測度の定義 (4/12)

### Function

[MeasureTheory.Function.SimpleFunc](MeasureTheory/Function/SimpleFunc.md) - 単関数の定義 (4/13)  
[MeasureTheory.Function.Lesbegue](MeasureTheory/Measure/Lesbegue.md) - lintegral (4/13)

## ProbabilityTheory