Filter.Basic

==========================

コード元
[Filter.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Basic.html)

このファイルではフィルタの基本的な性質を定義しています.

```
theorem Eventually.of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp
```

`Eventually.of_forall`は全てのxについてpが成り立てば, "十分大きな"xについてpが成り立つことを述べた主張です.ここで`mem_of_superset`と`univ_mem'`は以下の定理になります.

``` lean4
theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy

theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x
```

ちなみに`univ_mem'`の`fun x _ => h x`は`∀ x ∈ Set.univ, x ∈ s`ですが, `Set.Subset`の定義よりこれは`Set.univ ⊆ s`そのものです.