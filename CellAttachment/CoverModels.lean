module

public import CellAttachment.Annulus
public import CellAttachment.Embeddings
public import CellAttachment.CoverPushout
public import CellAttachment.Retraction
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section


/-! # Coordinate models of the genuine cover and its overlap

The interior open set is the actual coproduct of open disks; its intersection
with the punctured neighborhood is the actual coproduct of punctured open
disks. Component indices are locally constant and hence cannot change along
any path or fundamental-groupoid arrow.
-/

noncomputable section
open scoped ContinuousMap
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

theorem overlap_isOpen (f : ι → C(Circle, X)) : IsOpen (overlap f) :=
  (puncturedNeighborhood_isOpen f).inter (interiors_isOpen f)

/-- Forget puncturing while retaining the actual open-disk point. -/
def annulusInclusion : C(Annulus, OpenDisk) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The coproduct of punctured-disk inclusions. -/
def sigmaAnnulusInclusion : C((Σ _ : ι, Annulus), (Σ _ : ι, OpenDisk)) :=
  ⟨Sigma.map id (fun _ => annulusInclusion), Continuous.sigma_map
    (fun _ => annulusInclusion.continuous)⟩

lemma sigmaAnnulusInclusion_isEmbedding :
    Topology.IsEmbedding (sigmaAnnulusInclusion (ι := ι)) := by
  change Topology.IsEmbedding (Sigma.map (β₁ := fun _ : ι => Annulus) (β₂ := fun _ : ι => OpenDisk)
    (id : ι → ι) (fun _ => (Subtype.val : Annulus → OpenDisk)))
  exact (Topology.isEmbedding_sigmaMap Function.injective_id).mpr
    (fun _ => Topology.IsEmbedding.subtypeVal)

/-- Coordinates of punctured interior points in the actual quotient space. -/
def annulusInteriorMap (f : ι → C(Circle, X)) : C((Σ _ : ι, Annulus), Space f) :=
  (interiorMap f).comp sigmaAnnulusInclusion

@[simp] lemma annulusInteriorMap_apply (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) : annulusInteriorMap f z = interiorMap f ⟨z.1, z.2.1⟩ := rfl

lemma annulusInteriorMap_isEmbedding (f : ι → C(Circle, X)) :
    Topology.IsEmbedding (annulusInteriorMap f) :=
  (interiorMap_isOpenEmbedding f).isEmbedding.comp sigmaAnnulusInclusion_isEmbedding

/-- An interior coordinate belongs to the punctured neighborhood exactly when it is nonzero. -/
@[simp] lemma interiorMap_mem_puncturedNeighborhood_iff (f : ι → C(Circle, X))
    (i : ι) (z : OpenDisk) :
    interiorMap f ⟨i, z⟩ ∈ puncturedNeighborhood f ↔ (z : ℂ) ≠ 0 := by
  change quotientMap f (.inr ⟨i, ⟨z, z.property.le⟩⟩) ∉ centers f ↔ _
  simp only [quotient_inr_mem_centers]

/-- No assumed topology: the image of the actual punctured-disk embedding is the overlap. -/
lemma annulusInteriorMap_range (f : ι → C(Circle, X)) :
    Set.range (annulusInteriorMap f) = overlap f := by
  ext y
  constructor
  · rintro ⟨⟨i, z⟩, rfl⟩
    exact ⟨(interiorMap_mem_puncturedNeighborhood_iff f i z.1).mpr z.property,
      interiorRepresentative_mem_interiors f i z.1⟩
  · intro hy
    have hy' : y ∈ Set.range (interiorMap f) := by
      rw [interiorMap_range]
      exact hy.2
    obtain ⟨⟨i, z⟩, rfl⟩ := hy'
    have hz : (z : ℂ) ≠ 0 :=
      (interiorMap_mem_puncturedNeighborhood_iff f i z).mp hy.1
    exact ⟨⟨i, ⟨z, hz⟩⟩, rfl⟩

/-- The overlap, with its genuine induced quotient topology, is the annulus coproduct. -/
def overlapHomeomorph (f : ι → C(Circle, X)) :
    (Σ _ : ι, Annulus) ≃ₜ overlap f :=
  (annulusInteriorMap_isEmbedding f).toHomeomorph.trans
    (Homeomorph.setCongr (annulusInteriorMap_range f))

@[simp] lemma overlapHomeomorph_apply (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) : (overlapHomeomorph f z : Space f) = annulusInteriorMap f z := rfl

/-- The actual continuous inclusion of the overlap into the interior open set. -/
def overlapToInteriors (f : ι → C(Circle, X)) : C(overlap f, interiors f) :=
  ⟨fun z => ⟨z.1, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The actual continuous inclusion of the overlap into the punctured neighborhood. -/
def overlapToNeighborhood (f : ι → C(Circle, X)) : C(overlap f, puncturedNeighborhood f) :=
  ⟨fun z => ⟨z.1, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The coordinate square of the overlap inclusion commutes on the nose. -/
lemma overlapToInteriors_coordinates (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) :
    overlapToInteriors f (overlapHomeomorph f z) =
      interiorsHomeomorph f (sigmaAnnulusInclusion z) := rfl

/-- A single disk's actual open embedding into the quotient. -/
def cellInteriorMap (f : ι → C(Circle, X)) (i : ι) : C(OpenDisk, Space f) :=
  ⟨fun z => interiorMap f ⟨i, z⟩,
    (interiorMap f).continuous.comp continuous_sigmaMk⟩

/-- The genuine interior of an individual attached cell. -/
def cellInterior (f : ι → C(Circle, X)) (i : ι) : Set (Space f) :=
  Set.range (cellInteriorMap f i)

lemma cellInteriorMap_isOpenEmbedding (f : ι → C(Circle, X)) (i : ι) :
    Topology.IsOpenEmbedding (cellInteriorMap f i) :=
  (interiorMap_isOpenEmbedding f).comp Topology.IsOpenEmbedding.sigmaMk

lemma cellInterior_isOpen (f : ι → C(Circle, X)) (i : ι) : IsOpen (cellInterior f i) :=
  (cellInteriorMap_isOpenEmbedding f i).isOpen_range

/-- Each actual interior component is homeomorphic to the genuine open complex disk. -/
def cellInteriorHomeomorph (f : ι → C(Circle, X)) (i : ι) : OpenDisk ≃ₜ cellInterior f i :=
  (cellInteriorMap_isOpenEmbedding f i).isEmbedding.toHomeomorph

@[simp] lemma cellInteriorHomeomorph_apply (f : ι → C(Circle, X)) (i : ι) (z : OpenDisk) :
    (cellInteriorHomeomorph f i z : Space f) = cellInteriorMap f i z := rfl

/-- Contractibility of the actual quotient-subspace cell interior follows from its coordinates. -/
instance cellInterior_contractibleSpace (f : ι → C(Circle, X)) (i : ι) :
    ContractibleSpace (cellInterior f i) :=
  (cellInteriorHomeomorph f i).symm.contractibleSpace

instance cellInterior_simplyConnectedSpace (f : ι → C(Circle, X)) (i : ι) :
    SimplyConnectedSpace (cellInterior f i) := inferInstance

/-- A single punctured disk's actual embedding into the quotient. -/
def cellAnnulusMap (f : ι → C(Circle, X)) (i : ι) : C(Annulus, Space f) :=
  (cellInteriorMap f i).comp annulusInclusion

/-- The genuine overlap component in cell `i`. -/
def cellOverlap (f : ι → C(Circle, X)) (i : ι) : Set (Space f) :=
  overlap f ∩ cellInterior f i

lemma cellOverlap_isOpen (f : ι → C(Circle, X)) (i : ι) : IsOpen (cellOverlap f i) :=
  (overlap_isOpen f).inter (cellInterior_isOpen f i)

lemma cellAnnulusMap_isEmbedding (f : ι → C(Circle, X)) (i : ι) :
    Topology.IsEmbedding (cellAnnulusMap f i) :=
  (cellInteriorMap_isOpenEmbedding f i).isEmbedding.comp Topology.IsEmbedding.subtypeVal

lemma cellAnnulusMap_range (f : ι → C(Circle, X)) (i : ι) :
    Set.range (cellAnnulusMap f i) = cellOverlap f i := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ⟨z.1, rfl⟩⟩
    rw [← annulusInteriorMap_range]
    exact ⟨⟨i, z⟩, rfl⟩
  · intro hy
    obtain ⟨z, rfl⟩ := hy.2
    have hz : (z : ℂ) ≠ 0 :=
      (interiorMap_mem_puncturedNeighborhood_iff f i z).mp hy.1.1
    exact ⟨⟨z, hz⟩, rfl⟩

/-- Each actual overlap component is homeomorphic to the genuine punctured open disk. -/
def cellOverlapHomeomorph (f : ι → C(Circle, X)) (i : ι) : Annulus ≃ₜ cellOverlap f i :=
  (cellAnnulusMap_isEmbedding f i).toHomeomorph.trans
    (Homeomorph.setCongr (cellAnnulusMap_range f i))

@[simp] lemma cellOverlapHomeomorph_apply (f : ι → C(Circle, X)) (i : ι) (z : Annulus) :
    (cellOverlapHomeomorph f i z : Space f) = cellAnnulusMap f i z := rfl

instance cellOverlap_pathConnectedSpace (f : ι → C(Circle, X)) (i : ι) :
    PathConnectedSpace (cellOverlap f i) :=
  (cellOverlapHomeomorph f i).pathConnectedSpace

/-- The actual overlap component has its circle homotopy type by proved geometry. -/
def cellOverlapHomotopyEquivCircle (f : ι → C(Circle, X)) (i : ι) :
    cellOverlap f i ≃ₕ Circle :=
  (cellOverlapHomeomorph f i).symm.toHomotopyEquiv.trans annulusHomotopyEquivCircle

/-- The actual half-radius basepoint in cell `i`'s overlap. -/
def cellOverlapBasepoint (f : ι → C(Circle, X)) (i : ι) : cellOverlap f i :=
  cellOverlapHomeomorph f i annulusBasepoint

/-- The concrete half-radius loop in the actual quotient overlap component. -/
def cellOverlapGenerator (f : ι → C(Circle, X)) (i : ι) :
    Path (cellOverlapBasepoint f i) (cellOverlapBasepoint f i) :=
  annulusGenerator.map (cellOverlapHomeomorph f i).continuous

/-- Its actual based homotopy class. -/
def cellOverlapGeneratorClass (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup (cellOverlap f i) (cellOverlapBasepoint f i) :=
  .mk (cellOverlapGenerator f i)

/-- Coordinate transport is the induced isomorphism of actual based fundamental groups. -/
def cellOverlapFundamentalGroupEquivAnnulus (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup (cellOverlap f i) (cellOverlapBasepoint f i) ≃*
      FundamentalGroup Annulus annulusBasepoint :=
  homotopyEquivFundamentalGroupOfEq (cellOverlapHomeomorph f i).symm.toHomotopyEquiv
    ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint)

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma cellOverlapFundamentalGroupEquivAnnulus_generator
    (f : ι → C(Circle, X)) (i : ι) :
    cellOverlapFundamentalGroupEquivAnnulus f i (cellOverlapGeneratorClass f i) =
      annulusGeneratorClass := by
  change FundamentalGroup.mapOfEq
    ((cellOverlapHomeomorph f i).symm : C(cellOverlap f i, Annulus))
    ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint)
    (cellOverlapGeneratorClass f i) = _
  unfold cellOverlapGeneratorClass cellOverlapGenerator
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    (((cellOverlapGenerator f i).map (cellOverlapHomeomorph f i).symm.continuous).cast
      ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint).symm
      ((cellOverlapHomeomorph f i).symm_apply_apply annulusBasepoint).symm) = _
  congr 1
  apply Path.ext
  funext t
  exact (cellOverlapHomeomorph f i).symm_apply_apply (annulusGenerator t)

/-- Every actual overlap-component class is a power of the concrete half-radius loop. -/
theorem cellOverlapGenerator_generates (f : ι → C(Circle, X)) (i : ι)
    (γ : FundamentalGroup (cellOverlap f i) (cellOverlapBasepoint f i)) :
    ∃ n : ℤ, cellOverlapGeneratorClass f i ^ n = γ := by
  obtain ⟨n, hn⟩ := annulusGenerator_generates (cellOverlapFundamentalGroupEquivAnnulus f i γ)
  refine ⟨n, (cellOverlapFundamentalGroupEquivAnnulus f i).injective ?_⟩
  rw [map_zpow, cellOverlapFundamentalGroupEquivAnnulus_generator]
  exact hn

lemma cellInterior_subset_interiors (f : ι → C(Circle, X)) (i : ι) :
    cellInterior f i ⊆ interiors f := by
  rintro y ⟨z, rfl⟩
  exact interiorRepresentative_mem_interiors f i z

/-- A cell interior included into the full interior open set. -/
def cellInteriorToInteriors (f : ι → C(Circle, X)) (i : ι) :
    C(cellInterior f i, interiors f) :=
  ⟨fun z => ⟨z.1, cellInterior_subset_interiors f i z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- An overlap component included into the full overlap. -/
def cellOverlapToOverlap (f : ι → C(Circle, X)) (i : ι) :
    C(cellOverlap f i, overlap f) :=
  ⟨fun z => ⟨z.1, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- An overlap component included into its actual disk interior. -/
def cellOverlapToCellInterior (f : ι → C(Circle, X)) (i : ι) :
    C(cellOverlap f i, cellInterior f i) :=
  ⟨fun z => ⟨z.1, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- An overlap component included into the actual punctured neighborhood. -/
def cellOverlapToNeighborhood (f : ι → C(Circle, X)) (i : ι) :
    C(cellOverlap f i, puncturedNeighborhood f) :=
  (overlapToNeighborhood f).comp (cellOverlapToOverlap f i)

@[simp] lemma cellInteriorToInteriors_coordinates (f : ι → C(Circle, X)) (i : ι)
    (z : OpenDisk) :
    cellInteriorToInteriors f i (cellInteriorHomeomorph f i z) =
      interiorsHomeomorph f ⟨i, z⟩ := rfl

@[simp] lemma cellOverlapToOverlap_coordinates (f : ι → C(Circle, X)) (i : ι)
    (z : Annulus) :
    cellOverlapToOverlap f i (cellOverlapHomeomorph f i z) =
      overlapHomeomorph f ⟨i, z⟩ := rfl

@[simp] lemma cellOverlapToCellInterior_coordinates (f : ι → C(Circle, X)) (i : ι)
    (z : Annulus) :
    cellOverlapToCellInterior f i (cellOverlapHomeomorph f i z) =
      cellInteriorHomeomorph f i z.1 := rfl

/-- The neighborhood retraction on the overlap is exactly the original attaching map
applied to the polar coordinate, not an abstract homotopic replacement. -/
lemma neighborhoodRetraction_overlap_coordinates (f : ι → C(Circle, X)) (x₀ : X)
    (i : ι) (z : Annulus) :
    neighborhoodRetraction f x₀
      (overlapToNeighborhood f (overlapHomeomorph f ⟨i, z⟩)) = f i (annulusPolar z) := by
  change (if h : (z.1 : ℂ) ≠ 0 then f i (polar ⟨⟨z.1, z.1.property.le⟩, h⟩)
    else x₀) = _
  rw [dite_eq_left z.property]
  rfl

lemma neighborhoodRetraction_cellOverlap_coordinates (f : ι → C(Circle, X)) (x₀ : X)
    (i : ι) (z : Annulus) :
    neighborhoodRetraction f x₀
      (cellOverlapToNeighborhood f i (cellOverlapHomeomorph f i z)) = f i (annulusPolar z) :=
  neighborhoodRetraction_overlap_coordinates f x₀ i z

/-- The index projection from any topological coproduct is locally constant,
without giving the index type any additional structure. -/
lemma sigmaIndex_isLocallyConstant {A : ι → Type*} [∀ i, TopologicalSpace (A i)] :
    IsLocallyConstant (Sigma.fst : (Σ i, A i) → ι) :=
  fun S => isOpen_sigma_fst_preimage S

/-- The cell index of an actual interior point. -/
def interiorIndex (f : ι → C(Circle, X)) (z : interiors f) : ι :=
  ((interiorsHomeomorph f).symm z).1

/-- The cell index of an actual overlap point. -/
def overlapIndex (f : ι → C(Circle, X)) (z : overlap f) : ι :=
  ((overlapHomeomorph f).symm z).1

lemma interiorIndex_isLocallyConstant (f : ι → C(Circle, X)) :
    IsLocallyConstant (interiorIndex f) :=
  sigmaIndex_isLocallyConstant.comp_continuous (interiorsHomeomorph f).symm.continuous

lemma overlapIndex_isLocallyConstant (f : ι → C(Circle, X)) :
    IsLocallyConstant (overlapIndex f) :=
  sigmaIndex_isLocallyConstant.comp_continuous (overlapHomeomorph f).symm.continuous

@[simp] lemma interiorIndex_coordinates (f : ι → C(Circle, X))
    (z : Σ _ : ι, OpenDisk) : interiorIndex f (interiorsHomeomorph f z) = z.1 := by
  simp [interiorIndex]

@[simp] lemma overlapIndex_coordinates (f : ι → C(Circle, X))
    (z : Σ _ : ι, Annulus) : overlapIndex f (overlapHomeomorph f z) = z.1 := by
  simp [overlapIndex]

lemma interiorIndex_overlapToInteriors (f : ι → C(Circle, X)) (z : overlap f) :
    interiorIndex f (overlapToInteriors f z) = overlapIndex f z := by
  obtain ⟨z, rfl⟩ := (overlapHomeomorph f).surjective z
  rw [overlapToInteriors_coordinates, interiorIndex_coordinates, overlapIndex_coordinates]
  rfl

/-- A locally constant index cannot change anywhere along a continuous path. -/
lemma index_constant_along_path {A : Type*} [TopologicalSpace A] {j : A → ι}
    (hj : IsLocallyConstant j) {a b : A} (p : Path a b) (t : unitInterval) : j (p t) = j a := by
  have h := (hj.comp_continuous p.continuous).apply_eq_of_preconnectedSpace t 0
  simpa only [Function.comp_apply, p.source] using h

lemma interiorIndex_path (f : ι → C(Circle, X)) {a b : interiors f}
    (p : Path a b) (t : unitInterval) : interiorIndex f (p t) = interiorIndex f a :=
  index_constant_along_path (interiorIndex_isLocallyConstant f) p t

lemma overlapIndex_path (f : ι → C(Circle, X)) {a b : overlap f}
    (p : Path a b) (t : unitInterval) : overlapIndex f (p t) = overlapIndex f a :=
  index_constant_along_path (overlapIndex_isLocallyConstant f) p t

/-- Every actual interior groupoid arrow lies within a single disk component. -/
lemma interiorIndex_arrow (f : ι → C(Circle, X)) {a b : interiors f}
    (γ : Path.Homotopic.Quotient a b) : interiorIndex f a = interiorIndex f b := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  simpa only [p.target] using (interiorIndex_path f p 1).symm

/-- Every actual overlap groupoid arrow lies within a single annulus component. -/
lemma overlapIndex_arrow (f : ι → C(Circle, X)) {a b : overlap f}
    (γ : Path.Homotopic.Quotient a b) : overlapIndex f a = overlapIndex f b := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  simpa only [p.target] using (overlapIndex_path f p 1).symm

/-- The continuous second-coordinate projection of a constant-fiber coproduct. -/
def coproductSecond {A : Type*} [TopologicalSpace A] : C((Σ _ : ι, A), A) :=
  ⟨Sigma.snd, continuous_sigma (fun _ => continuous_id)⟩

/-- The continuous inclusion of one coproduct component. -/
def coproductComponent {A : Type*} [TopologicalSpace A] (i : ι) : C(A, (Σ _ : ι, A)) :=
  ⟨fun z : A => (⟨i, z⟩ : Σ _ : ι, A), by
    exact continuous_sigmaMk (σ := fun _ : ι => A) (i := i)⟩

/-- Mapping a loop in a coproduct component to its coordinate and back changes no path. -/
lemma coproduct_path_reconstruction {A : Type*} [TopologicalSpace A] (i : ι) (a : A)
    (p : Path (⟨i, a⟩ : Σ _ : ι, A) ⟨i, a⟩) :
    (p.map (coproductSecond (ι := ι)).continuous).map (coproductComponent i).continuous = p := by
  apply Path.ext
  funext t
  have hi : (p t).1 = i := index_constant_along_path sigmaIndex_isLocallyConstant p t
  exact Sigma.ext hi.symm (heq_of_eq rfl)

/-- Inclusion of one component induces the actual isomorphism on its based fundamental group. -/
def coproductFundamentalGroupEquiv {A : Type*} [TopologicalSpace A] (i : ι) (a : A) :
    FundamentalGroup A a ≃* FundamentalGroup (Σ _ : ι, A) ⟨i, a⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map (coproductComponent i) a) (by
    constructor
    · intro γ δ h
      have hr (ε : FundamentalGroup A a) :
          FundamentalGroup.map (coproductSecond (ι := ι)) ⟨i, a⟩
            (FundamentalGroup.map (coproductComponent i) a ε) = ε := by
        obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective ε
        change Path.Homotopic.Quotient.mk
          ((p.map (coproductComponent i).continuous).map (coproductSecond (ι := ι)).continuous) = _
        rfl
      have hh := congrArg (FundamentalGroup.map (coproductSecond (ι := ι)) ⟨i, a⟩) h
      exact (hr γ).symm.trans (hh.trans (hr δ))
    · intro γ
      obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
      refine ⟨Path.Homotopic.Quotient.mk (p.map (coproductSecond (ι := ι)).continuous), ?_⟩
      change Path.Homotopic.Quotient.mk
        ((p.map (coproductSecond (ι := ι)).continuous).map (coproductComponent i).continuous) = _
      rw [coproduct_path_reconstruction]
      rfl)

@[simp] lemma coproductFundamentalGroupEquiv_apply {A : Type*} [TopologicalSpace A]
    (i : ι) (a : A) (γ : FundamentalGroup A a) :
    coproductFundamentalGroupEquiv i a γ = FundamentalGroup.map (coproductComponent i) a γ := rfl

/-- The radius-half anchor of the actual full overlap in cell `i`. -/
def overlapAnchor (f : ι → C(Circle, X)) (i : ι) : overlap f :=
  overlapHomeomorph f ⟨i, annulusBasepoint⟩

/-- An actual path from its component's half-radius anchor to every overlap point. -/
def overlapAnchorPaths (f : ι → C(Circle, X)) (w : overlap f) :
    Path (overlapAnchor f (overlapIndex f w)) w :=
  ((PathConnectedSpace.somePath annulusBasepoint ((overlapHomeomorph f).symm w).2).map
    ((overlapHomeomorph f).continuous.comp (continuous_sigmaMk (i := overlapIndex f w)))).cast
      rfl ((overlapHomeomorph f).apply_symm_apply w).symm

/-- An actual path from the overlap anchor to every point of its disk component. -/
def interiorAnchorPaths (f : ι → C(Circle, X)) (v : interiors f) :
    Path (overlapRight f (overlapAnchor f (interiorIndex f v))) v :=
  ((PathConnectedSpace.somePath annulusBasepoint.1 ((interiorsHomeomorph f).symm v).2).map
    ((interiorsHomeomorph f).continuous.comp (continuous_sigmaMk (i := interiorIndex f v)))).cast
      rfl ((interiorsHomeomorph f).apply_symm_apply v).symm

/-- The full interior open set has trivial vertex groups, even when it is disconnected. -/
theorem interiorVertexGroup_subsingleton (f : ι → C(Circle, X)) (v : interiors f) :
    Subsingleton (FundamentalGroup (interiors f) v) := by
  let h := interiorsHomeomorph f
  let c := h.symm v
  let e := (homotopyEquivFundamentalGroup h.symm.toHomotopyEquiv v).trans
    (coproductFundamentalGroupEquiv c.1 c.2).symm
  exact e.injective.subsingleton

/-- The concrete half-radius generator in the actual full overlap. -/
def overlapAnchorGenerator (f : ι → C(Circle, X)) (i : ι) :
    Path (overlapAnchor f i) (overlapAnchor f i) :=
  annulusGenerator.map
    ((overlapHomeomorph f).continuous.comp (continuous_sigmaMk (i := i)))

/-- Its actual homotopy class at the overlap anchor. -/
def overlapAnchorGeneratorClass (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup (overlap f) (overlapAnchor f i) :=
  .mk (overlapAnchorGenerator f i)

/-- Component inclusion followed by the true overlap homeomorphism is an actual based isomorphism. -/
def overlapAnchorFundamentalGroupEquiv (f : ι → C(Circle, X)) (i : ι) :
    FundamentalGroup Annulus annulusBasepoint ≃*
      FundamentalGroup (overlap f) (overlapAnchor f i) :=
  (coproductFundamentalGroupEquiv i annulusBasepoint).trans
    (homotopyEquivFundamentalGroup (overlapHomeomorph f).toHomotopyEquiv ⟨i, annulusBasepoint⟩)

@[simp] lemma overlapAnchorFundamentalGroupEquiv_generator (f : ι → C(Circle, X)) (i : ι) :
    overlapAnchorFundamentalGroupEquiv f i annulusGeneratorClass = overlapAnchorGeneratorClass f i := by
  change Path.Homotopic.Quotient.mk
    ((annulusGenerator.map (coproductComponent i).continuous).map
      (overlapHomeomorph f).continuous) = _
  rfl

/-- Every actual full-overlap anchor loop class is a power of its concrete half-radius generator. -/
theorem overlapAnchorGenerator_generates (f : ι → C(Circle, X)) (i : ι)
    (γ : FundamentalGroup (overlap f) (overlapAnchor f i)) :
    ∃ n : ℤ, γ = overlapAnchorGeneratorClass f i ^ n := by
  obtain ⟨n, hn⟩ := annulusGenerator_generates ((overlapAnchorFundamentalGroupEquiv f i).symm γ)
  refine ⟨n, ?_⟩
  have h := congrArg (overlapAnchorFundamentalGroupEquiv f i) hn
  simpa only [map_zpow, overlapAnchorFundamentalGroupEquiv_generator,
    MulEquiv.apply_symm_apply] using h.symm

/-- The retracted overlap anchor is exactly the attaching map's basepoint. -/
@[simp] lemma neighborhoodRetraction_overlapAnchor (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    neighborhoodRetraction f x₀ (overlapLeft f (overlapAnchor f i)) = f i 1 := by
  change neighborhoodRetraction f x₀
    (overlapToNeighborhood f (overlapHomeomorph f ⟨i, annulusBasepoint⟩)) = _
  rw [neighborhoodRetraction_overlap_coordinates, annulusPolar_basepoint]

/-- The actual overlap generator retracts to the original attaching-circle loop,
with its actual endpoint equality displayed explicitly. -/
lemma neighborhoodRetraction_overlapAnchorGenerator (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    ((overlapAnchorGenerator f i).map
      ((neighborhoodRetraction f x₀).comp (overlapLeft f)).continuous).cast
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm =
      circleGenerator.map (f i).continuous := by
  apply Path.ext
  funext t
  change neighborhoodRetraction f x₀
    (overlapToNeighborhood f (overlapHomeomorph f ⟨i, annulusGenerator t⟩)) = f i (circleGenerator t)
  rw [neighborhoodRetraction_overlap_coordinates]
  exact congrArg (f i) (annulusPolar_halfCircle (circleGenerator t))

/-- The induced based map sends the actual overlap generator to the attaching class. -/
lemma neighborhoodRetraction_overlapAnchorGeneratorClass
    (f : ι → C(Circle, X)) (x₀ : X) (i : ι) :
    FundamentalGroup.mapOfEq ((neighborhoodRetraction f x₀).comp (overlapLeft f))
      (neighborhoodRetraction_overlapAnchor f x₀ i) (overlapAnchorGeneratorClass f i) =
      FundamentalGroup.map (f i) 1 circleGeneratorClass := by
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    (((overlapAnchorGenerator f i).map
      ((neighborhoodRetraction f x₀).comp (overlapLeft f)).continuous).cast
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm
        (neighborhoodRetraction_overlapAnchor f x₀ i).symm) = _
  rw [neighborhoodRetraction_overlapAnchorGenerator]
  rfl

end CellAttachment
