import CellAttachment.NormalForm

/-!
# The genuine two-open-set cover of an arbitrary cell attachment

The first open set omits exactly the disk centers. The second is the disjoint
union of all disk interiors. These facts use the quotient topology directly.
-/

noncomputable section
namespace CellAttachment
universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The center of the closed complex unit disk. -/
def diskCenter : Disk := ⟨0, by simp⟩
/-- The center viewed in the open disk. -/
def openDiskCenter : OpenDisk := ⟨0, by simp⟩

/-- The set of all attached disk interiors. -/
def interiors (f : ι → C(Circle, X)) : Set (Space f) :=
  {y | ∃ z : Σ _ : ι, OpenDisk, normalForm f y = .inr z}

/-- The set of attached disk centers, with no finiteness assumption. -/
def centers (f : ι → C(Circle, X)) : Set (Space f) :=
  {y | ∃ i : ι, normalForm f y = .inr ⟨i, openDiskCenter⟩}

/-- The punctured neighborhood of the original space. -/
def puncturedNeighborhood (f : ι → C(Circle, X)) : Set (Space f) := (centers f)ᶜ

@[simp] theorem inclusion_not_mem_interiors (f : ι → C(Circle, X)) (x : X) :
    inclusion f x ∉ interiors f := by simp [interiors]

@[simp] theorem interiorRepresentative_mem_interiors (f : ι → C(Circle, X))
    (i : ι) (z : OpenDisk) :
    quotientMap f (interiorRepresentative i z) ∈ interiors f := by
  exact ⟨⟨i, z⟩, normalForm_interiorRepresentative f i z⟩

@[simp] theorem inclusion_not_mem_centers (f : ι → C(Circle, X)) (x : X) :
    inclusion f x ∉ centers f := by simp [centers]

@[simp] theorem quotient_inl_mem_interiors (f : ι → C(Circle, X)) (x : X) :
    quotientMap f (.inl x) ∈ interiors f ↔ False := by
  change inclusion f x ∈ interiors f ↔ False
  simp

@[simp] theorem quotient_inr_mem_interiors (f : ι → C(Circle, X)) (i : ι) (z : Disk) :
    quotientMap f (.inr ⟨i, z⟩) ∈ interiors f ↔ ‖(z : ℂ)‖ < 1 := by
  change (∃ n, normalize f (.inr ⟨i, z⟩) = Sum.inr n) ↔ _
  by_cases h : ‖(z : ℂ)‖ = 1
  · simp [normalize, h]
  · simp [normalize, h, lt_of_le_of_ne z.property h]

@[simp] theorem quotient_inl_mem_centers (f : ι → C(Circle, X)) (x : X) :
    quotientMap f (.inl x) ∈ centers f ↔ False := by
  change inclusion f x ∈ centers f ↔ False
  simp

@[simp] theorem quotient_inr_mem_centers (f : ι → C(Circle, X)) (i : ι) (z : Disk) :
    quotientMap f (.inr ⟨i, z⟩) ∈ centers f ↔ (z : ℂ) = 0 := by
  change (∃ j, normalize f (.inr ⟨i, z⟩) = Sum.inr ⟨j, openDiskCenter⟩) ↔ _
  by_cases h : ‖(z : ℂ)‖ = 1
  · simp only [normalize, h, dite_true, Sum.inl_ne_inr, exists_false, false_iff]
    intro hz
    simpa [hz] using h
  · simp only [normalize, h, dite_false]
    constructor
    · rintro ⟨j, hj⟩
      have hz := congrArg (fun n : NormalForm X ι =>
        n.elim (fun _ => none) (fun w => some (w.2 : ℂ))) hj
      exact Option.some.inj hz
    · intro hz
      refine ⟨i, ?_⟩
      congr 2
      exact Subtype.ext hz

/-- Openness is checked on the unglued topological sum, component by component. -/
theorem interiors_isOpen (f : ι → C(Circle, X)) : IsOpen (interiors f) := by
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isOpen_preimage]
  rw [isOpen_sum_iff]
  constructor
  · convert isOpen_empty (X := X) using 1
    ext x
    simp
  · rw [isOpen_sigma_iff]
    intro i
    have hopen : IsOpen {z : Disk | ‖(z : ℂ)‖ < 1} :=
      isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
    convert hopen using 1
    ext z
    simp

/-- The set of centers is closed even when the original space is non-Hausdorff. -/
theorem centers_isClosed (f : ι → C(Circle, X)) : IsClosed (centers f) := by
  rw [← (quotientMap_isQuotientMap f).isCoinducing.isClosed_preimage]
  rw [isClosed_sum_iff]
  constructor
  · convert isClosed_empty (X := X) using 1
    ext x
    simp
  · rw [isClosed_sigma_iff]
    intro i
    have hclosed : IsClosed {z : Disk | (z : ℂ) = 0} :=
      isClosed_eq continuous_subtype_val continuous_const
    convert hclosed using 1
    ext z
    simp

theorem puncturedNeighborhood_isOpen (f : ι → C(Circle, X)) :
    IsOpen (puncturedNeighborhood f) := (centers_isClosed f).isOpen_compl

/-- The two genuine open sets cover the whole adjunction quotient. -/
theorem openCover_union (f : ι → C(Circle, X)) :
    puncturedNeighborhood f ∪ interiors f = Set.univ := by
  ext y
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : y ∈ centers f
  · right
    rcases h with ⟨i, hi⟩
    exact ⟨⟨i, openDiskCenter⟩, hi⟩
  · exact Or.inl h

end CellAttachment
