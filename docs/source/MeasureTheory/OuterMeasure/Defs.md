MeasureTheory.OuterMeasure.Defs
============================================

このファイルでは外測度を定義しています. また測度論に関する他のファイルをimportしていない測度論の最も基本的なファイルになります

コード元
[MeasureTheory.OuterMeasure.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Defs.html)

``` lean4
/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure OuterMeasure (α : Type*) where
  /-- Outer measure function. Use automatic coercion instead. -/
  protected measureOf : Set α → ℝ≥0∞
  protected empty : measureOf ∅ = 0
  protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
    measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
```
外測度は非負(`measureOf`), $\mu(\emptyset) = 0$ (`empty`), 単調性(`mono`), 可算劣加法性(`iUnion_nat`)により定義されます.
protectedによってOuterMeasure内部のフィールドをstructureと名前空間の外から参照することができないようになっています. 
またautomatic coercionにより`μ.measureOf s`を`μ s`とより直感的な形で書くことができます. 実際
``` lean4
@[simp] theorem measureOf_eq_coe (m : OuterMeasure α) : m.measureOf = m := rfl
```
が成り立っています.
`iUnion_nat`の`Pairwise (Disjoint on s)`の型について詳しくみていきます.
`Pairwise`の定義は
``` lean4
/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
def Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j
```
`Disjoint`の定義は
``` lean4
variable [PartialOrder α] [OrderBot α]

def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
```
`on`は名前空間`Function`内で定義されている関数で, `on`の定義は
``` lean4
/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
abbrev onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)

@[inherit_doc onFun]
scoped infixl:2 " on " => onFun
```
で`g`をそれぞれの引数に適用してから`f`を適用する関数です. 今回のDisjointの型は`Set α → Set α → Prop`であり, `on`を使うことで`Set α`の要素に対してDisjointを適用することができます. つまり`(Disjoint on s)`は`ℕ → ℕ → Prop`の型を持つので無事`Pairwise (Disjoint on s)`の型が`Prop`であることを確認できました.

``` lean4
This typeclass is used to unify some API for outer measures and measures. -/
class OuterMeasureClass (F : Type*) (α : outParam Type*) [FunLike F (Set α) ℝ≥0∞] : Prop where
  protected measure_empty (f : F) : f ∅ = 0
  protected measure_mono (f : F) {s t} : s ⊆ t → f s ≤ f t
  protected measure_iUnion_nat_le (f : F) (s : ℕ → Set α) : Pairwise (Disjoint on s) →
    f (⋃ i, s i) ≤ ∑' i, f (s i)
```
structureだけではなくclassも定義されています. 一般にstructureは具体的に定義をするのに対し, classは対象となる(structureも含む)型にある性質があるかどうかを示すために使われます. 例えばOuterMeasureClassはOuterMeasureの性質を持つ型のclassです. これはmeasureTheory.OuterMeasure.Defsに定義されている`measureOf`, `empty`, `mono`, `iUnion_nat`の性質を持つ型のclassです. これによりmeasureTheory.OuterMeasure.Defsで定義された`measureOf`, `empty`, `mono`, `iUnion_nat`の性質を持つ型はOuterMeasureClassに属することができます.

``` lean4
instance : OuterMeasureClass (OuterMeasure α) α where
  measure_empty f := f.empty
  measure_mono f := f.mono
  measure_iUnion_nat_le f := f.iUnion_nat
```
OuterMeasureはOuterMeasureの性質を持ちます.(当然)