Filter.Defs, Filter.Basic
============================================

このファイルではフィルタを定義しています. 測度の定義で使う部分を抜き出して説明します.

コード元
[Filter.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html)

## filterの定義

``` lean4
/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
```
フィルタは全体集合を含み(univ_sets), 上方向に閉じていて(sets_of_superset), 有限交叉に関して閉じている(inter_sets)集合族です.

## Eventually

``` lean4
/-- `f.Eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in atTop, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f

@[inherit_doc Filter.Eventually]
notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r
```

この定義は「述語pを満たす要素xの集合がフィルターfに属している」ことを表しています. この定義の妥当性を具体例を用いて説明します. 補集合が有限である自然数の集合の集合である補有限フィルターを考えます. このときpの補集合は有限であるため, 十分大きなxに対してpが成り立つことを意味します. `∀ᶠ`は`Eventually`の略記です.

``` lean4
theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy

theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x

theorem Eventually.of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp
```

`Eventually.of_forall`は全てのxについてpが成り立てば, "十分大きな"xについてpが成り立つことを述べた主張です.
ちなみに`univ_mem'`の`fun x _ => h x`は`∀ x ∈ Set.univ, x ∈ s`ですが, `Set.Subset`の定義よりこれは`Set.univ ⊆ s`そのものです.

``` lean4
Note that you should **not** use this definition directly, but instead write `s ⊆ t`. -/
protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
```

``` lean4
/-- Two functions `f` and `g` are *eventually equal* along a filter `l` if the set of `x` such that
`f x = g x` belongs to `l`. -/
def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x
```
`EventuallyEq`は`{x | f x = g x} ∈ l`と同じ意味です.

## filter_upwards

``` lean4
syntax (name := filterUpwards) "filter_upwards" (" [" term,* "]")?
  (" with" (ppSpace colGt term:max)*)? (" using " term)? : tactic

elab_rules : tactic
| `(tactic| filter_upwards $[[$[$args],*]]? $[with $wth*]? $[using $usingArg]?) => do
  let config : ApplyConfig := {newGoals := ApplyNewGoals.nonDependentOnly}
  for e in args.getD #[] |>.reverse do
    let goal ← getMainGoal
    replaceMainGoal <| ← goal.withContext <| runTermElab do
      let m ← mkFreshExprMVar none
      let lem ← Term.elabTermEnsuringType
        (← ``(Filter.mp_mem $e $(← Term.exprToSyntax m))) (← goal.getType)
      goal.assign lem
      return [m.mvarId!]
  liftMetaTactic fun goal => do
    goal.apply (← mkConstWithFreshMVarLevels ``Filter.univ_mem') config
  evalTactic <|← `(tactic| dsimp (config := {zeta := false}) only [Set.mem_setOf_eq])
  if let some l := wth then
    evalTactic <|← `(tactic| intro $[$l]*)
  if let some e := usingArg then
    evalTactic <|← `(tactic| exact $e)
```

TODO