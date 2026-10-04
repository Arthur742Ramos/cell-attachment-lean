module

public import CellAttachment.OpenCover
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section


/-!
# Genuine embeddings in the attaching quotient

The original space is a closed embedded subspace, without any separation
assumption on it. The coproduct of disk interiors is openly embedded. Both
proofs use the quotient topology and the explicit attaching relation.
-/

noncomputable section
namespace CellAttachment
universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Boundary inclusion is closed because its domain is compact and its
codomain is Hausdorff. This does not require any separation of the base. -/
theorem boundaryInclusion_isClosedMap : IsClosedMap boundaryInclusion :=
  boundaryInclusion.continuous.isClosedMap

/-- The part of a closed base image lying over a particular disk is exactly
its attaching-boundary preimage. -/
theorem quotient_inr_mem_inclusion_image (f : ι → C(Circle, X))
    (A : Set X) (i : ι) (z : Disk) :
    quotientMap f (.inr ⟨i, z⟩) ∈ inclusion f '' A ↔
      z ∈ boundaryInclusion '' ((f i) ⁻¹' A) := by
  constructor
  · rintro ⟨x, hx, heq⟩
    have hn := congrArg (normalForm f) heq
    change normalize f (.inl x) = normalize f (.inr ⟨i, z⟩) at hn
    by_cases hz : ‖(z : ℂ)‖ = 1
    · simp only [normalize, hz, dite_true, Sum.inl.injEq] at hn
      refine ⟨diskBoundaryPoint z hz, ?_, ?_⟩
      · change f i (diskBoundaryPoint z hz) ∈ A
        simpa only [← hn] using hx
      · rfl
    · simp only [normalize, hz, dite_false, Sum.inl_ne_inr] at hn
  · rintro ⟨w, hw, rfl⟩
    exact ⟨f i w, hw, (characteristic_boundary f i w).symm⟩

/-- Closed subsets of the original space have closed images in the quotient. -/
theorem inclusion_isClosedMap (f : ι → C(Circle, X)) : IsClosedMap (inclusion f) := by
  intro A hA
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isClosed_preimage]
  rw [isClosed_sum_iff]
  constructor
  · convert hA using 1
    ext x
    change inclusion f x ∈ inclusion f '' A ↔ x ∈ A
    exact (inclusion_injective f).mem_set_image
  · rw [isClosed_sigma_iff]
    intro i
    have hc := boundaryInclusion_isClosedMap ((f i) ⁻¹' A)
      (hA.preimage (f i).continuous)
    convert hc using 1
    ext z
    exact quotient_inr_mem_inclusion_image f A i z

/-- The original space is a closed embedded subspace for every attaching
family, including non-Hausdorff spaces and infinitely many disks. -/
theorem inclusion_isClosedEmbedding (f : ι → C(Circle, X)) :
    Topology.IsClosedEmbedding (inclusion f) :=
  .of_continuous_injective_isClosedMap (inclusion f).continuous
    (inclusion_injective f) (inclusion_isClosedMap f)

/-- The closed original-space image is exactly the complement of the
open disk interiors. -/
theorem inclusion_range_eq_compl_interiors (f : ι → C(Circle, X)) :
    Set.range (inclusion f) = (interiors f)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact inclusion_not_mem_interiors f x
  · intro hy
    obtain ⟨a, rfl⟩ := (quotientMap_isQuotientMap f).surjective y
    cases a with
    | inl x => exact ⟨x, rfl⟩
    | inr w =>
      rcases w with ⟨i, z⟩
      have hn : ¬ ‖(z : ℂ)‖ < 1 := by
        simpa only [Set.mem_compl_iff, quotient_inr_mem_interiors] using hy
      have hz : ‖(z : ℂ)‖ = 1 := le_antisymm z.property (le_of_not_gt hn)
      refine ⟨f i (diskBoundaryPoint z hz), ?_⟩
      exact (characteristic_boundary f i (diskBoundaryPoint z hz)).symm

/-- The original space is homeomorphic to its closed image. -/
def inclusionHomeomorph (f : ι → C(Circle, X)) :
    X ≃ₜ Set.range (inclusion f) :=
  (inclusion_isClosedEmbedding f).isEmbedding.toHomeomorph

@[simp] theorem inclusionHomeomorph_apply (f : ι → C(Circle, X)) (x : X) :
    (inclusionHomeomorph f x : Space f) = inclusion f x := rfl

/-- The canonical map from the open complex disk into the closed disk. -/
def openDiskInclusion : C(OpenDisk, Disk) where
  toFun z := ⟨z, z.property.le⟩
  continuous_toFun := by fun_prop

theorem openDiskInclusion_isOpenMap : IsOpenMap openDiskInclusion := by
  have h : IsOpen {z : ℂ | ‖z‖ < 1} := isOpen_lt continuous_norm continuous_const
  exact h.isOpenMap_subtype_val.subtype_mk (p := fun z : ℂ => ‖z‖ ≤ 1) (fun z => (z.property : ‖(z : ℂ)‖ < 1).le)

/-- The coproduct of all interiors, included in the unglued topological sum. -/
def rawInteriorMap : C((Σ _ : ι, OpenDisk), Raw X ι) where
  toFun z := interiorRepresentative z.1 z.2
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact continuous_inr.comp ((continuous_sigmaMk (i := i)).comp
      openDiskInclusion.continuous)

/-- Interior inclusion is open already before taking the attaching quotient. -/
theorem rawInteriorMap_isOpenMap : IsOpenMap (rawInteriorMap (X := X) (ι := ι)) := by
  rw [isOpenMap_sigma]
  intro i
  exact isOpenMap_inr.comp (isOpenMap_sigmaMk.comp openDiskInclusion_isOpenMap)

/-- The canonical continuous inclusion of the coproduct of open disks. -/
def interiorMap (f : ι → C(Circle, X)) : C((Σ _ : ι, OpenDisk), Space f) :=
  (quotientMap f).comp rawInteriorMap

@[simp] theorem interiorMap_apply (f : ι → C(Circle, X)) (z : Σ _ : ι, OpenDisk) :
    interiorMap f z = quotientMap f (interiorRepresentative z.1 z.2) := rfl

/-- A raw interior representative has no other raw representative in its
quotient class. Boundary gluings do not affect it. -/
theorem quotient_eq_interiorRepresentative_iff (f : ι → C(Circle, X))
    (a : Raw X ι) (i : ι) (z : OpenDisk) :
    quotientMap f a = quotientMap f (interiorRepresentative i z) ↔
      a = interiorRepresentative i z := by
  constructor
  · intro heq
    have hn := congrArg (normalForm f) heq
    rw [normalForm_interiorRepresentative] at hn
    change normalize f a = Sum.inr ⟨i, z⟩ at hn
    cases a with
    | inl x => simp only [normalize, Sum.inl_ne_inr] at hn
    | inr w =>
      rcases w with ⟨j, w⟩
      by_cases hw : ‖(w : ℂ)‖ = 1
      · simp only [normalize, hw, dite_true, Sum.inl_ne_inr] at hn
      · simp only [normalize, hw, dite_false, Sum.inr.injEq] at hn
        have hraw := congrArg (fun p : Σ _ : ι, OpenDisk =>
          normalRepresentative (X := X) (Sum.inr p)) hn
        exact hraw
  · rintro rfl
    rfl

/-- Images of sets of interior points are saturated without adding any
boundary or original-space points. -/
theorem interiorMap_image_preimage (f : ι → C(Circle, X))
    (S : Set (Σ _ : ι, OpenDisk)) :
    (quotientMap f) ⁻¹' (interiorMap f '' S) = rawInteriorMap '' S := by
  ext a
  constructor
  · rintro ⟨z, hz, heq⟩
    refine ⟨z, hz, ?_⟩
    exact ((quotient_eq_interiorRepresentative_iff f a z.1 z.2).mp heq.symm).symm
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- Interior images are open by checking their saturated raw preimages.
The global quotient map is not assumed to be open. -/
theorem interiorMap_isOpenMap (f : ι → C(Circle, X)) : IsOpenMap (interiorMap f) := by
  intro S hS
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage]
  rw [interiorMap_image_preimage]
  exact rawInteriorMap_isOpenMap S hS

/-- The entire coproduct of open disks openly embeds in the adjunction space. -/
theorem interiorMap_isOpenEmbedding (f : ι → C(Circle, X)) :
    Topology.IsOpenEmbedding (interiorMap f) :=
  .of_continuous_injective_isOpenMap (interiorMap f).continuous
    (interiors_injective f) (interiorMap_isOpenMap f)

/-- The range of the open embedding is precisely the open set of interiors. -/
theorem interiorMap_range (f : ι → C(Circle, X)) :
    Set.range (interiorMap f) = interiors f := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact interiorRepresentative_mem_interiors f z.1 z.2
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    obtain ⟨a, rfl⟩ := (quotientMap_isQuotientMap f).surjective y
    change normalize f a = Sum.inr z at hz
    exact (quotient_eq_iff_normalize_eq f _ _).mpr (by
      change normalize f (normalRepresentative (Sum.inr z)) = normalize f a
      rw [normalize_normalRepresentative f (Sum.inr z)]
      exact hz.symm)

/-- The disjoint union of disk interiors is homeomorphic to the actual
interior subspace, with its induced quotient topology. -/
def interiorsHomeomorph (f : ι → C(Circle, X)) :
    (Σ _ : ι, OpenDisk) ≃ₜ interiors f :=
  (interiorMap_isOpenEmbedding f).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (interiorMap_range f))

@[simp] theorem interiorsHomeomorph_apply (f : ι → C(Circle, X))
    (z : Σ _ : ι, OpenDisk) :
    (interiorsHomeomorph f z : Space f) = interiorMap f z := rfl

end CellAttachment
