module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section


/-
  This file contains lemmas about monotone paths in a preordered topological space
-/

open scoped unitInterval

lemma monotone_path_bounded_left {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t :=
    Eq.trans_le (id γ.source.symm) (hγ unitInterval.nonneg')

lemma monotone_path_bounded_right {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : γ t ≤ y :=
  calc
    γ t ≤ γ 1 := hγ (Subtype.coe_le_coe.mp (unitInterval.le_one t))
    _ = y := γ.target

lemma monotone_path_bounded {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t ∧ γ t ≤ y :=
  ⟨monotone_path_bounded_left hγ t, monotone_path_bounded_right hγ t⟩

lemma monotone_path_source_le_target {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) : x ≤ y :=
  calc
    x = γ 0 := γ.source.symm
    _ ≤ γ 1 := hγ (by norm_num : (0 : I) ≤ 1)
    _ = y := γ.target
