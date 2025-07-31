MeasureTheory.Function.HasFiniteIntegral
============================================

コード元
[MeasureTheory.Function.HasFiniteIntegral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.html)

``` lean4
variable [ENorm ε]

/-- `HasFiniteIntegral f μ` means that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `HasFiniteIntegral f` means `HasFiniteIntegral f volume`. -/
def HasFiniteIntegral {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
```

ここで, `‖ e ‖ₑ`はeの拡張(extended, ∞を含む)非負実数ノルムで以下のように定義されます.
``` lean4
/-- Auxiliary class, endowing a type `α` with a function `enorm : α → ℝ≥0∞` with notation `‖x‖ₑ`. -/
@[notation_class]
class ENorm (E : Type*) where
  /-- the `ℝ≥0∞`-valued norm function. -/
  enorm : E → ℝ≥0∞

@[inherit_doc] notation "‖" e "‖ₑ" => enorm e
```

``` lean4
variable [NormedAddCommGroup β]

theorem hasFiniteIntegral_iff_norm (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_enorm, ofReal_norm_eq_enorm]
```
`f`の値域が`NormedAddCommGroup`(ノルム付き可換群)である時, `HasFiniteIntegral`は`f`のノルムの絶対可積分性と同値です. これは以下の`ofReal_norm_eq_enorm`から従います. ここで`@[to_additive ofReal_norm_eq_enorm]`は, `E`をSeminormedGroupからSeminormedAddGroupに変え, `ofReal_norm_eq_enorm`の二項演算子`*`を`+`に変えたバージョンを生成するためのタグです. 

``` lean4
variable [SeminormedGroup E]

@[to_additive ofReal_norm_eq_enorm]
lemma ofReal_norm_eq_enorm' (a : E) : .ofReal ‖a‖ = ‖a‖ₑ := ENNReal.ofReal_eq_coe_nnreal _
```