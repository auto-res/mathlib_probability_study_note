MeasureTheory.OuterMeasure.Induced
============================================

コード元
[MeasureTheory.OuterMeasure.Induced](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Induced.html)

``` lean4
variable {α : Type*} {P : α → Prop}
variable (m : ∀ s : α, P s → ℝ≥0∞)

/-- We can trivially extend a function defined on a subclass of objects (with codomain `ℝ≥0∞`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
def extend (s : α) : ℝ≥0∞ :=
  ⨅ h : P s, m s h

theorem extend_eq {s : α} (h : P s) : extend m s = m s h := by simp [extend, h]
```
`extend`は$\{s ∈ α | P (s)\}$の値域で定義される関数をそうではない部分に対して$\infty$で拡張しています.
`extend_eq`は実は`iInf_pos`から直接従います.`iInf_pos`を詳しく見ていきます.
``` lean4
@[simp]
theorem iInf_pos {p : Prop} {f : p → α} (hp : p) : ⨅ h : p, f h = f hp :=
  le_antisymm (iInf_le _ _) (le_iInf fun _ => le_rfl)
```
`iInf_pos`の右辺のle_rflは以下の証明を行っています.
``` lean4
p : Prop
f : p → α
hp x✝ : p
⊢ f hp ≤ f x✝
```
ここで`hp x✝`はproof irrelevanceよりdefinitionally equalになっています.

以下の`extend_empty`は`extend_eq`から直ちに従います.
``` lean4
variable (P0 : P ∅) (m0 : m ∅ P0 = 0)

include P0 m0 in
theorem extend_empty : extend m ∅ = 0 :=
  (extend_eq _ P0).trans m0
```

``` lean4
variable {m : ∀ s : Set α, P s → ℝ≥0∞}
variable (P0 : P ∅) (m0 : m ∅ P0 = 0)

/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
def inducedOuterMeasure : OuterMeasure α :=
  OuterMeasure.ofFunction (extend m) (extend_empty P0 m0)
```

`inducedOuterMeasure`について型の確認を行います. `ofFunction`は以下のように定義されています.

``` lean4
MeasureTheory.OuterMeasure.ofFunction.{u_1} {α : Type u_1} (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0) : OuterMeasure α
```
