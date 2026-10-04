module

public import CellAttachment.Adjunction

@[expose] public section


/-!
# Algebraic normal forms in the genuine attaching quotient

These normal forms classify quotient points. They do not replace the quotient
topology by a disjoint-union topology and are not asserted to be continuous.
-/

noncomputable section
namespace CellAttachment
universe u v

abbrev OpenDisk := {z : ℂ // ‖z‖ < 1}
abbrev NormalForm (X : Type u) (ι : Type v) := X ⊕ (Σ _ : ι, OpenDisk)

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The representative of an interior disk point in the raw disjoint union. -/
def interiorRepresentative (i : ι) (z : OpenDisk) : Raw X ι :=
  .inr ⟨i, ⟨z, z.property.le⟩⟩

/-- Interior points remain points of their unique disk; boundary points go to X. -/
def normalize (f : ι → C(Circle, X)) : Raw X ι → NormalForm X ι
  | .inl x => .inl x
  | .inr ⟨i, z⟩ =>
      if h : ‖(z : ℂ)‖ = 1 then .inl (f i (diskBoundaryPoint z h))
      else .inr ⟨i, ⟨z, lt_of_le_of_ne z.property h⟩⟩

theorem normalize_respects (f : ι → C(Circle, X)) {a b : Raw X ι}
    (h : AttachingRel f a b) : normalize f a = normalize f b := by
  cases h with
  | boundary i z =>
    change (if h : ‖(z : ℂ)‖ = 1 then (Sum.inl (f i (diskBoundaryPoint (boundaryInclusion z) h)) : NormalForm X ι)
      else Sum.inr ⟨i, _⟩) = Sum.inl (f i z)
    rw [dite_eq_left (Circle.norm_coe z)]
    rfl

/-- A well-defined algebraic normal form for every quotient point. -/
def normalForm (f : ι → C(Circle, X)) : Space f → NormalForm X ι :=
  Quot.lift (normalize f) (fun _ _ h => normalize_respects f h)

/-- Pick the raw representative of a normal form. -/
def normalRepresentative : NormalForm X ι → Raw X ι
  | .inl x => .inl x
  | .inr ⟨i, z⟩ => interiorRepresentative i z

@[simp] theorem normalize_normalRepresentative (f : ι → C(Circle, X))
    (n : NormalForm X ι) : normalize f (normalRepresentative n) = n := by
  cases n with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i, z⟩
    change (if h : ‖(z : ℂ)‖ = 1 then _ else _) = _
    rw [dite_eq_right (ne_of_lt z.property)]

/-- Normalization changes a representative only by prescribed boundary gluings. -/
theorem quotient_normalRepresentative_normalize (f : ι → C(Circle, X)) (a : Raw X ι) :
    quotientMap f (normalRepresentative (normalize f a)) = quotientMap f a := by
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i, z⟩
    by_cases h : ‖(z : ℂ)‖ = 1
    · simp only [normalize, h, dite_true, normalRepresentative]
      exact (Quot.sound (.boundary i (diskBoundaryPoint z h))).symm
    · simp only [normalize, h, dite_false, normalRepresentative, interiorRepresentative]

/-- Equality in the adjunction quotient is exactly equality of the algebraic normal forms. -/
theorem quotient_eq_iff_normalize_eq (f : ι → C(Circle, X)) (a b : Raw X ι) :
    quotientMap f a = quotientMap f b ↔ normalize f a = normalize f b := by
  constructor
  · exact fun h => congrArg (normalForm f) h
  · intro h
    rw [← quotient_normalRepresentative_normalize f a,
      ← quotient_normalRepresentative_normalize f b, h]

/-- Every interior point has its own unchanged normal form. -/
@[simp] theorem normalForm_interiorRepresentative (f : ι → C(Circle, X)) (i : ι) (z : OpenDisk) :
    normalForm f (quotientMap f (interiorRepresentative i z)) = .inr ⟨i, z⟩ :=
  normalize_normalRepresentative f (.inr ⟨i, z⟩)

@[simp] theorem normalForm_inclusion (f : ι → C(Circle, X)) (x : X) :
    normalForm f (inclusion f x) = .inl x := rfl

/-- All disk interiors embed algebraically as a disjoint family. -/
theorem interiors_injective (f : ι → C(Circle, X)) :
    Function.Injective (fun z : Σ _ : ι, OpenDisk =>
      quotientMap f (interiorRepresentative z.1 z.2)) := by
  intro a b h
  have h' := congrArg (normalForm f) h
  simpa using h'

/-- No interior point is identified with an original point. -/
theorem interior_ne_inclusion (f : ι → C(Circle, X)) (i : ι) (z : OpenDisk) (x : X) :
    quotientMap f (interiorRepresentative i z) ≠ inclusion f x := by
  intro h
  have h' := congrArg (normalForm f) h
  simpa using h'

end CellAttachment
