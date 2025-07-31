ProbabilityTheory.Independence.Kernel
=========================================

このファイルではカーネルによって独立性を定義していきます.


``` lean4
/-- A family of sets of sets `π : ι → Set (Set Ω)` is independent with respect to a kernel `κ` and
a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `∀ᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`.
It will be used for families of pi_systems. -/
def iIndepSets {_mΩ : MeasurableSpace Ω}
    (π : ι → Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (_H : ∀ i, i ∈ s → f i ∈ π i),
  ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i ∈ s, κ a (f i)
```
添え字付きの集合族`π`が独立であるとは, 任意の有限個の添え字の集合`{i_1, ..., i_n}`に対して, その添え字に対応する集合`f i_1, ..., f i_n`が`π i_1, ..., π i_n`に属するならば, `∀ᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i ∈ s, κ a (f i)`が成り立つことと定義します.

``` lean4
/-- Two sets of sets `s₁, s₂` are independent with respect to a kernel `κ` and a measure `μ` if for
any sets `t₁ ∈ s₁, t₂ ∈ s₂`, then `∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def IndepSets {_mΩ : MeasurableSpace Ω}
    (s1 s2 : Set (Set Ω)) (κ : Kernel α Ω) (μ : Measure α := by volume_tac) : Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → (∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2)
```
集合族`s1`と`s2`が独立であるとは, 任意の集合`t1 ∈ s1, t2 ∈ s2`に対して, `∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2`が成り立つことと定義します.

``` lean4
/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
kernel `κ` and a measure `μ` if the family of sets of measurable sets they define is independent. -/
def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndepSets (fun x ↦ {s | MeasurableSet[m x] s}) κ μ
```
添え字付きの可測空間族`m`が独立であるとは, 任意の添え字`x`に対して, `m x`が定める可測集合の族が独立であることと定義します.

``` lean4
/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
kernel `κ` and a measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def Indep (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  IndepSets {s | MeasurableSet[m₁] s} {s | MeasurableSet[m₂] s} κ μ
```
添え字付きの可測空間族`m₁, m₂`が独立であるとは, 任意の集合`t1 ∈ m₁, t2 ∈ m₂`に対して, `∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2`が成り立つことと定義します.