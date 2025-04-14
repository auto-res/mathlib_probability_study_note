Mathlib probability study note documentation
============================================

このドキュメントはMathlib4の[確率論](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability)と[測度論](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/MeasureTheory)の内容を理解するための勉強ノートです. 基礎的な部分(特に定義)を理解することを目標にします. 目次の順番は依存関係を意識しています. 今後の予定については[こちら](plan.md).

どなたでも編集や投稿を歓迎します.
特にfilter_upwardとvolume_tacの説明をしてくださる方を探しています.

## Filter
[Filter.Defs](Filter/Defs.md) - フィルタに関する概念 (4/12)  
[Filter.Basic](Filter/Basic.md) - フィルタの基本的な性質 (4/12)

## MeasureTheory

### Outer Measure

[MeasureTheory.OuterMeasure.Defs](MeasureTheory/OuterMeasure/Defs.md) - 外測度の定義 (4/7)  
[MeasureTheory.OuterMeasure.AE](MeasureTheory/OuterMeasure/AE.md) - Almost everywhereの定義 (4/8)
[MeasureTheory.OuterMeasure.OfFunction](MeasureTheory/OuterMeasure/OfFunction.md) - 外測度の別定義 (4/12)
[MeasureTheory.OuterMeasure.Induced](MeasureTheory/OuterMeasure/Induced.md) - 外測度の可測集合への制限 (4/12)

### MeasurableSpace

[MeasureTheory.MeasurableSpace.Defs](MeasureTheory/MeasurableSpace/Defs.md) - 可測空間, 可測関数の定義 (4/9)  
[MeasureTheory.MeasurableSpace.Basic](MeasureTheory/MeasurableSpace/Basic.md) - 可測空間の基本的な性質 (4/12)

### Measure

[MeasureTheory.Measure.MeasureSpaceDef](MeasureTheory/Measure/MeasureSpaceDef.md) - 測度の定義 (4/12)

### Function

[MeasureTheory.Function.SimpleFunc](MeasureTheory/Function/SimpleFunc.md) - 単関数の定義 (4/13)  
[MeasureTheory.Function.Lesbegue](MeasureTheory/Measure/Lesbegue.md) - lintegral (4/13)
[MeasureTheory.Function.HasFiniteIntegral](MeasureTheory/Function/HasFiniteIntegral.md) - 絶対可積分性の定義
[MeasureTheory.Function.Integrable](MeasureTheory/Function/Integrable.md) - 可積分性の定義

## ProbabilityTheory

# 参考文献(本)
- [ルベーグ積分入門](https://www.shokabo.co.jp/mybooks/ISBN978-4-7853-1304-3.html) - カラテオドリの公理論的測度論で参考にしました.
- [Analysis in Banach Spaces](https://link.springer.com/book/10.1007/978-3-319-48520-1) - ボホナー積分で参考にしました.
- [Foundations of Modern Probability](https://link.springer.com/book/10.1007/978-3-030-61871-1) - 確率論の基礎付けで参考にしました.