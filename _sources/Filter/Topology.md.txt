Filter.Topology
=========================
このファイルでは位相空間におけるフィルタの定義を行っています.

コード元
[Filter.Topology](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)

``` lean4
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Filter
open scoped Topology

/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ {s : Set X | x ∈ s ∧ IsOpen s}, Filter.principal s
```

`nhds`は点`x`の近傍を表すフィルタです. `x`を含む開集合の上に生成されるフィルタの下限を取ることで定義されます.