module

public import CellAttachment.Main

/-!
# Compiled adversarial tests for genuine two-cell attachment

These are proved expected outcomes, rather than bare invocations of exactness.
The general tests have no finiteness, separation, CW, or local-connectivity
hypotheses. Both the empty and constant families preserve the actual
inclusion-induced fundamental-group map, with arbitrary chosen whiskers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CellAttachment.Examples
universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- An empty family generates the trivial subgroup, without path-connectedness. -/
theorem empty_normalClosure [IsEmpty ι] (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) :
    attachingNormalClosure f x₀ γ = ⊥ := by
  simp [attachingNormalClosure, Set.range_eq_empty]

/-- For an empty family, the actual inclusion has trivial kernel and is bijective. -/
theorem empty_inclusionPi1 [IsEmpty ι] [PathConnectedSpace X]
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)) :
    (inclusionPi1 f x₀).ker = ⊥ ∧ Function.Bijective (inclusionPi1 f x₀) := by
  obtain ⟨hs, hk⟩ := cell_attachment_exact f x₀ γ
  have hb : (inclusionPi1 f x₀).ker = ⊥ := hk.trans (empty_normalClosure f x₀ γ)
  exact ⟨hb, (inclusionPi1 f x₀).ker_eq_bot_iff.mp hb, hs⟩

/-- The empty-family isomorphism is exactly the actual inclusion on every element. -/
def empty_inclusionPi1Equiv [IsEmpty ι] [PathConnectedSpace X]
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)) :
    FundamentalGroup X x₀ ≃* FundamentalGroup (Space f) (inclusion f x₀) :=
  MulEquiv.ofBijective (inclusionPi1 f x₀) (empty_inclusionPi1 f x₀ γ).2

@[simp] theorem empty_inclusionPi1Equiv_apply [IsEmpty ι] [PathConnectedSpace X]
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1))
    (g : FundamentalGroup X x₀) :
    empty_inclusionPi1Equiv f x₀ γ g = inclusionPi1 f x₀ g := rfl

/-- The constant family may have any index cardinality, and its values may vary. -/
def constantFamily (y : ι → X) : ι → C(Circle, X) :=
  fun i => ContinuousMap.const Circle (y i)

/-- A constant attaching map has trivial whiskered loop even for arbitrary whiskers.
No simple-connectedness, separation, or path-connectedness is used here. -/
theorem constant_attachingLoopClass (y : ι → X) (x₀ : X)
    (γ : ∀ i, Path x₀ (y i)) (i : ι) :
    attachingLoopClass (constantFamily y) x₀ γ i = 1 := by
  have hm : circleGenerator.map (constantFamily y i).continuous = Path.refl (y i) := by
    apply Path.ext
    funext t
    rfl
  change Path.Homotopic.Quotient.mk
      ((γ i).trans ((circleGenerator.map (constantFamily y i).continuous).trans (γ i).symm)) =
    Path.Homotopic.Quotient.refl x₀
  rw [hm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.mk_symm]
  exact Path.Homotopic.Quotient.trans_symm _

/-- Every constant family has trivial relator normal closure, even when infinite. -/
theorem constant_normalClosure (y : ι → X) (x₀ : X)
    (γ : ∀ i, Path x₀ (y i)) :
    attachingNormalClosure (constantFamily y) x₀ γ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨i, rfl⟩
  exact Subgroup.mem_bot.mpr (constant_attachingLoopClass y x₀ γ i)

/-- Attaching any family of constant two-cells preserves the actual fundamental group. -/
theorem constant_inclusionPi1 [PathConnectedSpace X] (y : ι → X) (x₀ : X)
    (γ : ∀ i, Path x₀ (y i)) :
    (inclusionPi1 (constantFamily y) x₀).ker = ⊥ ∧
      Function.Bijective (inclusionPi1 (constantFamily y) x₀) := by
  obtain ⟨hs, hk⟩ := cell_attachment_exact (constantFamily y) x₀ γ
  have hb : (inclusionPi1 (constantFamily y) x₀).ker = ⊥ :=
    hk.trans (constant_normalClosure y x₀ γ)
  exact ⟨hb, (inclusionPi1 (constantFamily y) x₀).ker_eq_bot_iff.mp hb, hs⟩

/-- The constant-family equivalence is the actual inclusion, not an abstract isomorphism. -/
def constant_inclusionPi1Equiv [PathConnectedSpace X] (y : ι → X) (x₀ : X)
    (γ : ∀ i, Path x₀ (y i)) :
    FundamentalGroup X x₀ ≃*
      FundamentalGroup (Space (constantFamily y)) (inclusion (constantFamily y) x₀) :=
  MulEquiv.ofBijective (inclusionPi1 (constantFamily y) x₀)
    (constant_inclusionPi1 y x₀ γ).2

@[simp] theorem constant_inclusionPi1Equiv_apply [PathConnectedSpace X]
    (y : ι → X) (x₀ : X) (γ : ∀ i, Path x₀ (y i)) (g : FundamentalGroup X x₀) :
    constant_inclusionPi1Equiv y x₀ γ g = inclusionPi1 (constantFamily y) x₀ g := rfl

/-- Concrete empty index with arbitrary path-connected original space. -/
theorem empty_index_bijective [PathConnectedSpace X] (x₀ : X) :
    Function.Bijective (inclusionPi1 (fun i : Empty => nomatch i) x₀) :=
  (empty_inclusionPi1 (fun i : Empty => nomatch i) x₀ (fun i => nomatch i)).2

/-- One constant two-cell preserves π₁, even with a nontrivial chosen whisker. -/
theorem singleton_constant [PathConnectedSpace X] (x₀ y : X) (γ : Path x₀ y) :
    attachingNormalClosure (constantFamily (fun _ : Unit => y)) x₀ (fun _ => γ) = ⊥ ∧
      Function.Bijective (inclusionPi1 (constantFamily (fun _ : Unit => y)) x₀) :=
  ⟨constant_normalClosure (fun _ : Unit => y) x₀ (fun _ => γ),
    (constant_inclusionPi1 (fun _ : Unit => y) x₀ (fun _ => γ)).2⟩

/-- Genuinely infinitely many two-cells, on an arbitrary path-connected X. -/
theorem countably_infinite_constant [PathConnectedSpace X] (x₀ : X)
    (y : ℕ → X) (γ : ∀ n, Path x₀ (y n)) :
    attachingNormalClosure (constantFamily y) x₀ γ = ⊥ ∧
      Function.Bijective (inclusionPi1 (constantFamily y) x₀) :=
  ⟨constant_normalClosure y x₀ γ, (constant_inclusionPi1 y x₀ γ).2⟩

/-- Repeating every attaching map twice does not change its relator normal closure. -/
theorem repeated_normalClosure (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) :
    attachingNormalClosure (fun p : ι × Bool => f p.1) x₀ (fun p => γ p.1) =
      attachingNormalClosure f x₀ γ := by
  unfold attachingNormalClosure
  congr 1
  ext g
  constructor
  · rintro ⟨⟨i, b⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(i, false), rfl⟩

/-- Exactness gives the same kernel for the actual maps into the two different quotients. -/
theorem repeated_inclusionPi1_kernel [PathConnectedSpace X]
    (f : ι → C(Circle, X)) (x₀ : X) (γ : ∀ i, Path x₀ (f i 1)) :
    (inclusionPi1 (fun p : ι × Bool => f p.1) x₀).ker = (inclusionPi1 f x₀).ker := by
  rw [(cell_attachment_exact (fun p : ι × Bool => f p.1) x₀ (fun p => γ p.1)).2,
    repeated_normalClosure f x₀ γ, (cell_attachment_exact f x₀ γ).2]

/-- Every constant circle map is genuinely noninjective: `-1` and `1` coincide. -/
theorem constant_map_not_injective (y : X) :
    ¬ Function.Injective (ContinuousMap.const Circle y) := by
  intro h
  exact Circle.neg_ne_self 1 (h (show
    ContinuousMap.const Circle y (-1) = ContinuousMap.const Circle y 1 by rfl))

/-- The duplicated family is noninjective even if the original family was injective. -/
theorem repeated_family_not_injective [Nonempty ι] (f : ι → C(Circle, X)) :
    ¬ Function.Injective (fun p : ι × Bool => f p.1) := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hp : (i, false) = (i, true) := h rfl
  have hb : false = true := congrArg Prod.snd hp
  cases hb

/-- A Type-0 original space and a genuinely infinite Type-1 index. -/
theorem index_higher_pi1_bijective :
    Function.Bijective (inclusionPi1
      (constantFamily (fun _ : ULift.{1} ℕ => (() : Unit))) ()) :=
  (constant_inclusionPi1 (fun _ : ULift.{1} ℕ => (() : Unit)) ()
    (fun _ => Path.refl ())).2

/-- The opposite universe ordering: a Type-1 original space and Type-0 infinite index. -/
theorem space_higher_pi1_bijective :
    Function.Bijective (inclusionPi1
      (constantFamily (fun _ : ℕ => (ULift.up () : ULift.{1} Unit))) (ULift.up ())) :=
  (constant_inclusionPi1 (fun _ : ℕ => (ULift.up () : ULift.{1} Unit)) (ULift.up ())
    (fun _ => Path.refl (ULift.up ()))).2

/-- Direct test of the full quotient theorem with the index universe higher. -/
theorem index_higher_quotient_compatible :
    let f := constantFamily (fun _ : ULift.{1} ℕ => (() : Unit))
    let γ := fun _ : ULift.{1} ℕ => Path.refl (() : Unit)
    ∃ e : FundamentalGroup Unit () ⧸ attachingNormalClosure f () γ ≃*
      FundamentalGroup (Space f) (inclusion f ()),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f () γ)) =
        inclusionPi1 f () :=
  (two_cell_attachment.{0,1}
    (constantFamily (fun _ : ULift.{1} ℕ => (() : Unit))) ()
      (fun _ => Path.refl ())).2.2

/-- Direct test of the full quotient theorem with the original-space universe higher. -/
theorem space_higher_quotient_compatible :
    let x₀ := (ULift.up () : ULift.{1} Unit)
    let f := constantFamily (fun _ : ℕ => x₀)
    let γ := fun _ : ℕ => Path.refl x₀
    ∃ e : FundamentalGroup (ULift.{1} Unit) x₀ ⧸ attachingNormalClosure f x₀ γ ≃*
      FundamentalGroup (Space f) (inclusion f x₀),
      e.toMonoidHom.comp (QuotientGroup.mk' (attachingNormalClosure f x₀ γ)) =
        inclusionPi1 f x₀ :=
  (two_cell_attachment.{1,0}
    (constantFamily (fun _ : ℕ => (ULift.up () : ULift.{1} Unit))) (ULift.up ())
      (fun _ => Path.refl (ULift.up ()))).2.2

/-- A two-point finite carrier, with the indiscrete topology rather than Bool's default. -/
def IndiscreteTwo : Type := Bool

instance : TopologicalSpace IndiscreteTwo := ⊤
instance : IndiscreteTopology IndiscreteTwo := ⟨rfl⟩
instance : Nonempty IndiscreteTwo := ⟨false⟩
instance : Finite IndiscreteTwo := inferInstanceAs (Finite Bool)

/-- Path-connectedness comes from the indiscrete topology; no Hausdorffness is present. -/
instance : PathConnectedSpace IndiscreteTwo := by infer_instance

/-- The test space is provably non-Hausdorff (indeed it is not even T₀). -/
theorem indiscreteTwo_not_t0 : ¬ T0Space IndiscreteTwo := by
  intro h
  let := h
  have hs : Subsingleton IndiscreteTwo := subsingleton_iff_indiscreteTopology.mpr inferInstance
  have hb' : (false : IndiscreteTwo) = true := @Subsingleton.elim IndiscreteTwo hs _ _
  have hb : (false : Bool) = true := hb'
  cases hb

theorem indiscreteTwo_not_t2 : ¬ T2Space IndiscreteTwo := by
  intro h
  let := h
  exact indiscreteTwo_not_t0 inferInstance

/-- Any family, including nonconstant maps, leaves the attached space's π₁ trivial. -/
theorem indiscreteTwo_arbitrary_family (f : ι → C(Circle, IndiscreteTwo))
    (x₀ : IndiscreteTwo) (γ : ∀ i, Path x₀ (f i 1)) :
    Subsingleton (FundamentalGroup (Space f) (inclusion f x₀)) := by
  obtain ⟨hs, _⟩ := cell_attachment_exact f x₀ γ
  refine ⟨fun a b => ?_⟩
  obtain ⟨p, rfl⟩ := hs a
  obtain ⟨q, rfl⟩ := hs b
  exact congrArg (inclusionPi1 f x₀) (Subsingleton.elim p q)

/-- A genuinely nonconstant map is continuous into the indiscrete two-point space. -/
def nonconstantIndiscreteMap : C(Circle, IndiscreteTwo) := by
  classical
  exact ⟨fun z => if z = 1 then false else true, continuous_of_indiscreteTopology⟩

theorem nonconstantIndiscreteMap_nonconstant :
    nonconstantIndiscreteMap (-1) ≠ nonconstantIndiscreteMap 1 := by
  classical
  change (if (-1 : Circle) = 1 then (false : Bool) else true) ≠
    (if (1 : Circle) = 1 then false else true)
  simp [Circle.neg_ne_self]

/-- Infinite, repeated, nonconstant attaching maps on a provably non-Hausdorff space. -/
theorem indiscreteTwo_infinite_nonconstant :
    Subsingleton (FundamentalGroup
      (Space (fun _ : ℕ => nonconstantIndiscreteMap))
      (inclusion (fun _ : ℕ => nonconstantIndiscreteMap) (false : IndiscreteTwo))) :=
  indiscreteTwo_arbitrary_family (fun _ : ℕ => nonconstantIndiscreteMap) (false : IndiscreteTwo)
    (fun _ => PathConnectedSpace.somePath (X := IndiscreteTwo) false (nonconstantIndiscreteMap 1))

end CellAttachment.Examples
