ProbabilityTheory.ConditionalProbability
=========================================

このファイルでは条件つき確率を形式化します.

``` lean4
variable (μ) in
/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s`
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`. -/
def cond (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s
```

`μ.restrict s`は`μ`を`s`に制限した測度であり, `μ s`はsに制限したあとの全測度になります.

``` lean4
@[inherit_doc ProbabilityTheory.cond]
scoped macro:max μ:term noWs "[|" s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s)
@[inherit_doc cond]
scoped macro:max μ:term noWs "[" t:term " | " s:term "]" : term =>
  `(ProbabilityTheory.cond $μ $s $t)
```

`cond μ s`は`μ[|s]`と書くことができ, `cond μ s t`は`μ[t|s]`と書くことができます.

ここで`μ.restrict s`は`μ`を`s`に制限した`t`の測度は`s`と`t`の共通部分の測度になります.(Measure.Restrictファイル)

``` lean4
/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `Measure.restrict_apply'`. -/
@[simp]
theorem restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t ∩ s) :=
  restrict_apply₀ ht.nullMeasurableSet
```

`restrict_apply`を用いるとよく見る条件つき確率の定義を導出することができます.

``` lean4
/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
theorem cond_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply' hms, Set.inter_comm, smul_eq_mul]
```

`μ`が有限測度の場合は, ベイズの定理も成り立ちます.

``` lean4
/-- **Bayes' Theorem** -/
theorem cond_eq_inv_mul_cond_mul (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω)
    [IsFiniteMeasure μ] : μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t := by
  rw [mul_assoc, cond_mul_eq_inter hmt s, Set.inter_comm, cond_apply hms]
```