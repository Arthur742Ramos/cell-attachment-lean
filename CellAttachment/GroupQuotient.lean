import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Algebraic quotient tools for cell attachment

This file contains only group-theoretic results. In particular, it does not assume or
claim that any topological attachment induces a surjective fundamental-group map or
has a specified kernel. Once those geometric assertions have been established, the
results here produce the quotient equivalence and its compatibility with the map.
-/

namespace CellAttachment

universe u v w

variable {G : Type u} [Group G] {H : Type v} [Group H] {ι : Type w}

/-- Killing every member of a family is equivalent to killing its normal closure. -/
theorem normalClosure_range_le_ker_iff (r : ι → G) (f : G →* H) :
    Subgroup.normalClosure (Set.range r) ≤ f.ker ↔ ∀ i, f (r i) = 1 := by
  constructor
  · intro h i
    exact MonoidHom.mem_ker.mp (h (Subgroup.subset_normalClosure (Set.mem_range_self i)))
  · intro h
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact MonoidHom.mem_ker.mpr (h i)

/-- A homomorphism killing the relators descends to the quotient by their normal closure. -/
def liftNormalClosure (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1) :
    G ⧸ Subgroup.normalClosure (Set.range r) →* H :=
  QuotientGroup.lift _ f ((normalClosure_range_le_ker_iff r f).mpr h)

@[simp]
theorem liftNormalClosure_mk (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1)
    (g : G) :
    liftNormalClosure r f h (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g) =
      f g := rfl

/-- The descended homomorphism commutes with the quotient projection. -/
@[simp]
theorem liftNormalClosure_comp_mk (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1) :
    (liftNormalClosure r f h).comp
      (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))) = f := rfl

/-- The descended homomorphism is uniquely determined by this compatibility. -/
theorem liftNormalClosure_unique (r : ι → G) (f : G →* H) (h : ∀ i, f (r i) = 1)
    (k : G ⧸ Subgroup.normalClosure (Set.range r) →* H)
    (hk : k.comp (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))) = f) :
    k = liftNormalClosure r f h := by
  apply QuotientGroup.monoidHom_ext
  rw [hk, liftNormalClosure_comp_mk]

/-- The compatible first-isomorphism equivalence, after a surjective map and its
kernel have been identified by a separate argument. -/
noncomputable def quotientNormalClosureEquiv (r : ι → G) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.normalClosure (Set.range r)) :
    G ⧸ Subgroup.normalClosure (Set.range r) ≃* H :=
  QuotientGroup.liftEquiv _ hf hker.symm

@[simp]
theorem quotientNormalClosureEquiv_mk (r : ι → G) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.normalClosure (Set.range r))
    (g : G) :
    quotientNormalClosureEquiv r f hf hker
      (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g) = f g := rfl

/-- Compatibility in homomorphism form, suitable for a commutative diagram. -/
@[simp]
theorem quotientNormalClosureEquiv_comp_mk (r : ι → G) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.normalClosure (Set.range r)) :
    (quotientNormalClosureEquiv r f hf hker).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))) = f := rfl

/-- Exactness identifies precisely which elements the original map kills. -/
theorem map_eq_one_iff_mem_normalClosure (r : ι → G) (f : G →* H)
    (hker : f.ker = Subgroup.normalClosure (Set.range r)) (g : G) :
    f g = 1 ↔ g ∈ Subgroup.normalClosure (Set.range r) := by
  rw [← hker]
  exact MonoidHom.mem_ker.symm

/-- Independently replacing the generators by conjugate elements does not change
normal closure. This is the algebraic part of independence from whiskering paths. -/
theorem normalClosure_range_eq_of_isConj (r s : ι → G)
    (h : ∀ i, IsConj (r i) (s i)) :
    Subgroup.normalClosure (Set.range r) = Subgroup.normalClosure (Set.range s) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨s i, Set.mem_range_self i, (h i).symm⟩)
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨r i, Set.mem_range_self i, h i⟩)

/-- A separate conjugating element may be chosen for every generator. -/
theorem normalClosure_range_conjugate (r c : ι → G) :
    Subgroup.normalClosure (Set.range (fun i => c i * r i * (c i)⁻¹)) =
      Subgroup.normalClosure (Set.range r) := by
  symm
  apply normalClosure_range_eq_of_isConj
  intro i
  exact isConj_iff.mpr ⟨c i, rfl⟩

/-- The normal closure is also independent of the orientation of all generators. -/
theorem normalClosure_range_inverse (r : ι → G) :
    Subgroup.normalClosure (Set.range (fun i => (r i)⁻¹)) =
      Subgroup.normalClosure (Set.range r) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact (Subgroup.normalClosure (Set.range r)).inv_mem
      (Subgroup.subset_normalClosure (Set.mem_range_self i))
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    have h : (r i)⁻¹ ∈ Subgroup.normalClosure (Set.range (fun j => (r j)⁻¹)) :=
      Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact (Subgroup.inv_mem_iff _).mp h

/-- Changing independently chosen conjugating paths induces the identity-on-
representatives equivalence between the corresponding quotient groups. -/
def quotientNormalClosureConjugateEquiv (r c : ι → G) :
    G ⧸ Subgroup.normalClosure (Set.range (fun i => c i * r i * (c i)⁻¹)) ≃*
      G ⧸ Subgroup.normalClosure (Set.range r) :=
  QuotientGroup.quotientMulEquivOfEq (normalClosure_range_conjugate r c)

@[simp]
theorem quotientNormalClosureConjugateEquiv_mk (r c : ι → G) (g : G) :
    quotientNormalClosureConjugateEquiv r c
      (QuotientGroup.mk' (Subgroup.normalClosure
        (Set.range (fun i => c i * r i * (c i)⁻¹))) g) =
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g := rfl

end CellAttachment
