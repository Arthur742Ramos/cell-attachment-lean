module

public import CellAttachment.GroupQuotient
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section


/-!
# Vertex-group tools for a categorical van Kampen square

These are abstract groupoid lemmas. They do not assert that a particular cell-attachment
space has the required open cover, connectivity, or disk and annulus homotopy types.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CellAttachment

universe u v

variable {W U V P : Type u}
variable [Groupoid.{v} W] [Groupoid.{v} U] [Groupoid.{v} V] [Groupoid.{v} P]

/-- Changing the vertex of a groupoid by a chosen path is a group isomorphism. -/
noncomputable def transportEnd {a b : U} (p : a ⟶ b) : End b ≃* End a where
  toFun g := p ≫ g ≫ inv p
  invFun g := inv p ≫ g ≫ p
  left_inv g := by simp [Category.assoc]
  right_inv g := by simp [Category.assoc]
  map_mul' g h := by simp [End.mul_def, Category.assoc]

/-- A loop at an overlap vertex, transported to the chosen vertex on the left. -/
noncomputable def overlapLoop (i : W ⥤ U) (b : U) (w : W)
    (p : b ⟶ i.obj w) (g : End w) : End b :=
  transportEnd p (i.map g)

/-- Equality of functors transports the assertion that an endomorphism is trivial. -/
theorem map_eq_id_of_functor_eq {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F G : C ⥤ D) (h : F = G) (x : C) (a : End x)
    (ha : G.map a = 𝟙 (G.obj x)) : F.map a = 𝟙 (F.obj x) := by
  subst G
  exact ha

/-- The commutative square kills transported overlap loops whenever the right-hand
vertex group is trivial. Only commutativity, rather than the universal property,
is needed for this direction. -/
theorem map_overlapLoop_eq_one (i : W ⥤ U) (k : W ⥤ V)
    (j : U ⥤ P) (l : V ⥤ P) (h : i ⋙ j = k ⋙ l)
    (b : U) (w : W) (p : b ⟶ i.obj w) (g : End w)
    (hg : k.map g = 𝟙 (k.obj w)) :
    j.mapEnd b (overlapLoop i b w p g) = 1 := by
  have hh : j.map (i.map g) = 𝟙 (j.obj (i.obj w)) := by
    exact map_eq_id_of_functor_eq (i ⋙ j) (k ⋙ l) h w g
      (by change l.map (k.map g) = 𝟙 (l.obj (k.obj w)); rw [hg, l.map_id])
  simp [overlapLoop, transportEnd, Functor.map_comp, hh]

/-- A Cat pushout with simply connected right-hand components kills the normal
closure of any chosen family of transported overlap loops. This is a proved
kernel inclusion, not an assumption identifying the entire kernel. -/
theorem normalClosure_overlapLoops_le_ker (i : W ⥤ U) (k : W ⥤ V)
    (j : U ⥤ P) (l : V ⥤ P)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (hV : ∀ v : V, Subsingleton (End v))
    (b : U) {ι : Type u} (w : ι → W)
    (p : ∀ a, b ⟶ i.obj (w a)) (r : ∀ a, End (w a)) :
    Subgroup.normalClosure (Set.range (fun a => overlapLoop i b (w a) (p a) (r a))) ≤
      (j.mapEnd b).ker := by
  apply (normalClosure_range_le_ker_iff _ _).mpr
  intro a
  apply map_overlapLoop_eq_one i k j l
    (congrArg Cat.Hom.toFunctor h.w) b (w a) (p a) (r a)
  exact (hV (k.obj (w a))).elim _ _

/-- Any compatible functor out of the left-hand groupoid detects relations in
its vertex group: relations imposed by the pushout must also hold in its target. -/
theorem pushout_kernel_le_kernel {D : Type u} [Category.{v} D]
    (i : W ⥤ U) (k : W ⥤ V) (j : U ⥤ P) (l : V ⥤ P)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (F : U ⥤ D) (K : V ⥤ D) (hFK : i ⋙ F = k ⋙ K) (b : U) :
    (j.mapEnd b).ker ≤ (F.mapEnd b).ker := by
  let d : P ⥤ D := (h.desc F.toCatHom K.toCatHom
    (Cat.ext hFK)).toFunctor
  have hd : j ⋙ d = F :=
    congrArg Cat.Hom.toFunctor (h.inl_desc F.toCatHom K.toCatHom (Cat.ext hFK))
  intro g hg
  apply MonoidHom.mem_ker.mpr
  change F.map g = 𝟙 (F.obj b)
  apply map_eq_id_of_functor_eq F (j ⋙ d) hd.symm b g
  change d.map (j.map g) = 𝟙 (d.obj (j.obj b))
  have hg' : j.map g = 𝟙 (j.obj b) := MonoidHom.mem_ker.mp hg
  rw [hg']
  exact d.map_id _

/-- Cyclic overlap vertex groups reduce every overlap-coordinate calculation
to killing the transported generator. The two overlap vertices may be joined
to a common component representative by different chosen paths. -/
theorem overlap_coordinate_eq_one_of_cyclic
    (i : W ⥤ U) (b : U) (w₀ x y : W) (a : b ⟶ i.obj w₀)
    (p : w₀ ⟶ x) (s : w₀ ⟶ y) (f : x ⟶ y) (r : End w₀)
    (hcyc : ∀ g : End w₀, ∃ n : ℤ, g = r ^ n)
    {G : Type v} [Group G] (q : End b →* G)
    (hr : q (overlapLoop i b w₀ a r) = 1) :
    q ((a ≫ i.map p) ≫ i.map f ≫ inv (a ≫ i.map s)) = 1 := by
  let e : End w₀ →* End b := (transportEnd a).toMonoidHom.comp (i.mapEnd w₀)
  have hcoord : ((a ≫ i.map p) ≫ i.map f ≫ inv (a ≫ i.map s) : End b) =
      e (p ≫ f ≫ inv s) := by
    simp [e, transportEnd, Functor.map_comp, Category.assoc]
  rw [hcoord]
  obtain ⟨n, hn⟩ := hcyc (p ≫ f ≫ inv s)
  rw [hn, e.map_zpow, q.map_zpow]
  change q (overlapLoop i b w₀ a r) ^ n = 1
  rw [hr, one_zpow]

attribute [local instance] uliftCategory

/-- The one-object groupoid placed in the object universe of the van Kampen
square. Its morphisms are still the elements of `G`. -/
abbrev VertexTarget (G : Type v) [Group G] := ULift.{u} (SingleObj G)

/-- A choice of paths from a vertex turns a homomorphism on its vertex group
into a functor on the whole connected groupoid. -/
noncomputable def basedFunctor (b : U) (p : ∀ x : U, b ⟶ x)
    {G : Type v} [Group G] (q : End b →* G) : U ⥤ VertexTarget.{u,v} G where
  obj _ := ⟨SingleObj.star G⟩
  map {x y} f := q (p x ≫ f ≫ inv (p y))
  map_id x := by
    change q (p x ≫ 𝟙 x ≫ inv (p x)) = 1
    simpa using q.map_one
  map_comp {x y z} f g := by
    change q (p x ≫ (f ≫ g) ≫ inv (p z)) =
      q (p y ≫ g ≫ inv (p z)) * q (p x ≫ f ≫ inv (p y))
    rw [← q.map_mul]
    simp [End.mul_def, Category.assoc]

/-- At the chosen vertex, normalized chosen paths recover the original group
homomorphism exactly. -/
theorem basedFunctor_map_base (b : U) (p : ∀ x : U, b ⟶ x)
    (hp : p b = 𝟙 b) {G : Type v} [Group G] (q : End b →* G) (g : End b) :
    (basedFunctor b p q).map g = q g := by
  simp [basedFunctor, hp]

/-- The based functor has precisely the original homomorphism's kernel. -/
theorem basedFunctor_ker (b : U) (p : ∀ x : U, b ⟶ x)
    (hp : p b = 𝟙 b) {G : Type v} [Group G] (q : End b →* G) :
    ((basedFunctor b p q).mapEnd b).ker = q.ker := by
  ext g
  change (basedFunctor b p q).map g = 1 ↔ q g = 1
  rw [basedFunctor_map_base b p hp q]

/-- If every arrow in the overlap becomes trivial in the quotient-coordinate
functor, it agrees there with the constant functor on the right-hand groupoid.
This condition is the concrete remaining annulus calculation, not a claim
that the attachment theorem is already established. -/
theorem basedFunctor_overlap_eq_const (i : W ⥤ U) (k : W ⥤ V)
    (b : U) (p : ∀ x : U, b ⟶ x) {G : Type v} [Group G] (q : End b →* G)
    (hoverlap : ∀ (x y : W) (f : x ⟶ y),
      q (p (i.obj x) ≫ i.map f ≫ inv (p (i.obj y))) = 1) :
    i ⋙ basedFunctor b p q =
      k ⋙ (Functor.const V).obj (ULift.up (SingleObj.star G)) := by
  apply Functor.hext
  · intro x
    rfl
  · intro x y f
    apply heq_of_eq
    exact hoverlap x y f

/-- A Cat pushout gives the reverse kernel inclusion without assuming a
surjective vertex-group map. The geometric inputs still required are normalized
paths in the left groupoid and the explicit quotient calculation on overlap arrows. -/
theorem pushout_kernel_le_normalClosure
    (i : W ⥤ U) (k : W ⥤ V) (j : U ⥤ P) (l : V ⥤ P)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (b : U) (p : ∀ x : U, b ⟶ x) (hp : p b = 𝟙 b)
    {ι : Type u} (r : ι → End b)
    (hoverlap : ∀ (x y : W) (f : x ⟶ y),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))
        (p (i.obj x) ≫ i.map f ≫ inv (p (i.obj y))) = 1) :
    (j.mapEnd b).ker ≤ Subgroup.normalClosure (Set.range r) := by
  let N := Subgroup.normalClosure (Set.range r)
  let q : End b →* End b ⧸ N := QuotientGroup.mk' N
  have hle := pushout_kernel_le_kernel i k j l h (basedFunctor b p q)
    ((Functor.const V).obj (ULift.up (SingleObj.star (End b ⧸ N))))
    (basedFunctor_overlap_eq_const i k b p q hoverlap) b
  rw [basedFunctor_ker b p hp q] at hle
  change (j.mapEnd b).ker ≤ (QuotientGroup.mk' N).ker at hle
  rw [QuotientGroup.ker_mk'] at hle
  exact hle

section ArrowDescent

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- A natural transformation regarded as a functor into the arrow category. -/
def natTransArrow {F G : C ⥤ D} (a : F ⟶ G) : C ⥤ Arrow D where
  obj x := Arrow.mk (a.app x)
  map f := Arrow.homMk (F.map f) (G.map f) (a.naturality f)
  map_id x := by
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply Arrow.hom_ext <;> simp

@[simp] theorem natTransArrow_left {F G : C ⥤ D} (a : F ⟶ G) :
    natTransArrow a ⋙ Arrow.leftFunc = F := rfl

@[simp] theorem natTransArrow_right {F G : C ⥤ D} (a : F ⟶ G) :
    natTransArrow a ⋙ Arrow.rightFunc = G := rfl

/-- Natural transformations glue across a strict categorical pushout. Encoding
them by functors into an arrow category derives this from the ordinary universal
property, rather than assuming a bicategorical pushout theorem. -/
theorem pushout_natTrans_exists
    {A B C D E : Type u} [Category.{u} A] [Category.{u} B]
    [Category.{u} C] [Category.{u} D] [Category.{u} E]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (F G : D ⥤ E) (a : j ⋙ F ⟶ j ⋙ G) (b : l ⋙ F ⟶ l ⋙ G)
    (hab : i ⋙ natTransArrow a = k ⋙ natTransArrow b) :
    ∃ t : F ⟶ G, whiskerLeft j t = a ∧ whiskerLeft l t = b := by
  let d : D ⥤ Arrow E := (h.desc (natTransArrow a).toCatHom
    (natTransArrow b).toCatHom (Cat.ext hab)).toFunctor
  have hdj : j ⋙ d = natTransArrow a :=
    congrArg Cat.Hom.toFunctor (h.inl_desc (natTransArrow a).toCatHom (natTransArrow b).toCatHom (Cat.ext hab))
  have hdl : l ⋙ d = natTransArrow b :=
    congrArg Cat.Hom.toFunctor (h.inr_desc (natTransArrow a).toCatHom (natTransArrow b).toCatHom (Cat.ext hab))
  have hF : d ⋙ Arrow.leftFunc = F := by
    apply (Functor.equivCatHom D E).injective
    apply h.hom_ext
    · apply Cat.ext
      change (j ⋙ d) ⋙ Arrow.leftFunc = j ⋙ F
      rw [hdj, natTransArrow_left]
    · apply Cat.ext
      change (l ⋙ d) ⋙ Arrow.leftFunc = l ⋙ F
      rw [hdl, natTransArrow_left]
  have hG : d ⋙ Arrow.rightFunc = G := by
    apply (Functor.equivCatHom D E).injective
    apply h.hom_ext
    · apply Cat.ext
      change (j ⋙ d) ⋙ Arrow.rightFunc = j ⋙ G
      rw [hdj, natTransArrow_right]
    · apply Cat.ext
      change (l ⋙ d) ⋙ Arrow.rightFunc = l ⋙ G
      rw [hdl, natTransArrow_right]
  let t : F ⟶ G := eqToHom hF.symm ≫ whiskerLeft d Arrow.leftToRight ≫ eqToHom hG
  refine ⟨t, ?_, ?_⟩
  · ext x
    have he : Arrow.mk (d.obj (j.obj x)).hom = Arrow.mk (a.app x) := by
      rw [Arrow.mk_eq]
      exact Functor.congr_obj hdj x
    obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp he
    dsimp [t]
    simp only [eqToHom_app, Arrow.leftToRight_app]
    rw [hh]
    cat_disch
  · ext x
    have he : Arrow.mk (d.obj (l.obj x)).hom = Arrow.mk (b.app x) := by
      rw [Arrow.mk_eq]
      exact Functor.congr_obj hdl x
    obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp he
    dsimp [t]
    simp only [eqToHom_app, Arrow.leftToRight_app]
    rw [hh]
    cat_disch

/-- Interpret a group homomorphism into a vertex group as a constant-object
functor from the universe-lifted one-object groupoid. -/
def vertexFunctor {D : Type u} [Category.{u} D] (x : D)
    {Q : Type u} [Group Q] (e : Q →* End x) : VertexTarget.{u,u} Q ⥤ D where
  obj _ := x
  map f := e f
  map_id _ := e.map_one
  map_comp f g := e.map_mul g f

/-- A glued, basepoint-normalized contraction proves surjectivity of the actual
left inclusion on vertex groups. Its hypotheses are functors and compatible
path transformations, not surjectivity or a prescribed kernel for that map. -/
theorem pushout_mapEnd_surjective_of_contraction
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) {Q : Type u} [Group Q] (q : End x →* Q)
    (hq : Function.Surjective q) (e : Q →* End (j.obj x))
    (he : e.comp q = j.mapEnd x) (d : D ⥤ VertexTarget.{u,u} Q)
    (a : j ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ j ⋙ 𝟭 D)
    (b : l ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ l ⋙ 𝟭 D)
    (hab : i ⋙ natTransArrow a = k ⋙ natTransArrow b)
    (ha : a.app x = 𝟙 (j.obj x)) : Function.Surjective (j.mapEnd x) := by
  obtain ⟨t, ht, _⟩ := pushout_natTrans_exists i k j l h
    (d ⋙ vertexFunctor (j.obj x) e) (𝟭 D) a b hab
  have htbase : t.app (j.obj x) = 𝟙 (j.obj x) := by
    have hh := congrArg (fun s => s.app x) ht
    exact hh.trans ha
  intro g
  have hn := t.naturality g
  change e (d.map g) ≫ t.app (j.obj x) = t.app (j.obj x) ≫ g at hn
  rw [htbase] at hn
  have hn' : e (d.map g) = g :=
    (Category.comp_id (e (d.map g))).symm.trans (hn.trans (Category.id_comp g))
  obtain ⟨z, hz⟩ := hq (d.map g)
  refine ⟨z, ?_⟩
  have hez := DFunLike.congr_fun he z
  change e (q z) = j.map z at hez
  change j.map z = g
  rw [← hez, hz]
  exact hn'

/-- Paths on the left provide the local contraction of the quotient
reconstruction functor. -/
noncomputable def reconstructionLeft
    {B D : Type u} [Groupoid.{u} B] [Groupoid.{u} D]
    (j : B ⥤ D) (x : B) (p : ∀ y : B, x ⟶ y)
    {Q : Type u} [Group Q] (q : End x →* Q) (e : Q →* End (j.obj x))
    (he : e.comp q = j.mapEnd x) (d : D ⥤ VertexTarget.{u,u} Q)
    (hd : j ⋙ d = basedFunctor x p q) :
    j ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ j ⋙ 𝟭 D where
  app y := j.map (p y)
  naturality y z f := by
    change e (d.map (j.map f)) ≫ j.map (p z) = j.map (p y) ≫ j.map f
    have hm : d.map (j.map f) = q (p y ≫ f ≫ inv (p z)) :=
      congrArg (fun T : B ⥤ VertexTarget.{u,u} Q => (T.map f : Q)) hd
    have he' := DFunLike.congr_fun he (p y ≫ f ≫ inv (p z))
    change e (q (p y ≫ f ≫ inv (p z))) = j.map (p y ≫ f ≫ inv (p z)) at he'
    rw [hm, he', ← j.map_comp, ← j.map_comp]
    congr 1
    simp [Category.assoc]

/-- Paths on a simply connected right-hand component provide its local
contraction. Naturality of the chosen paths is a concrete groupoid condition. -/
noncomputable def reconstructionRight
    {B C D : Type u} [Groupoid.{u} B] [Groupoid.{u} C] [Groupoid.{u} D]
    (j : B ⥤ D) (l : C ⥤ D) (x : B) {Q : Type u} [Group Q]
    (e : Q →* End (j.obj x)) (d : D ⥤ VertexTarget.{u,u} Q)
    (hd : l ⋙ d = (Functor.const C).obj (ULift.up (SingleObj.star Q)))
    (p : ∀ y : C, j.obj x ⟶ l.obj y)
    (hp : ∀ (y z : C) (f : y ⟶ z), p y ≫ l.map f = p z) :
    l ⋙ (d ⋙ vertexFunctor (j.obj x) e) ⟶ l ⋙ 𝟭 D where
  app y := p y
  naturality y z f := by
    change e (d.map (l.map f)) ≫ p z = p y ≫ l.map f
    have hm : d.map (l.map f) = (1 : Q) :=
      congrArg (fun T : C ⥤ VertexTarget.{u,u} Q => (T.map f : Q)) hd
    rw [hm, e.map_one]
    change 𝟙 (j.obj x) ≫ p z = p y ≫ l.map f
    rw [Category.id_comp]
    exact (hp y z f).symm

/-- Local path contractions agree on the overlap when their chosen paths
agree there. Endpoint transports are recorded as heterogeneous equality. -/
theorem reconstruction_overlap
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (hc : i ⋙ j = k ⋙ l) (x : B) (p : ∀ y : B, x ⟶ y)
    {Q : Type u} [Group Q] (q : End x →* Q) (e : Q →* End (j.obj x))
    (he : e.comp q = j.mapEnd x) (d : D ⥤ VertexTarget.{u,u} Q)
    (hdj : j ⋙ d = basedFunctor x p q)
    (hdl : l ⋙ d = (Functor.const C).obj (ULift.up (SingleObj.star Q)))
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    i ⋙ natTransArrow (reconstructionLeft j x p q e he d hdj) =
      k ⋙ natTransArrow (reconstructionRight j l x e d hdl c hn) := by
  let objEq : ∀ w : A,
      (i ⋙ natTransArrow (reconstructionLeft j x p q e he d hdj)).obj w =
        (k ⋙ natTransArrow (reconstructionRight j l x e d hdl c hn)).obj w := fun w => by
    change Arrow.mk (j.map (p (i.obj w))) = Arrow.mk (c (k.obj w))
    apply Arrow.ext (f := Arrow.mk (j.map (p (i.obj w))))
      (g := Arrow.mk (c (k.obj w))) rfl (Functor.congr_obj hc w)
    exact (conj_eqToHom_iff_heq _ _ rfl (Functor.congr_obj hc w)).mpr (hw w)
  refine CategoryTheory.Functor.ext objEq ?_
  intro w z f
  apply Arrow.hom_ext
  · simp only [Arrow.comp_left, Arrow.eqToHom_left]
    have hm := congrArg (fun T : A ⥤ D => e (d.map (T.map f))) hc
    simpa only [Functor.comp_map, natTransArrow, reconstructionLeft,
      reconstructionRight, vertexFunctor, Arrow.homMk_left, eqToHom_refl, Category.id_comp,
      Category.comp_id] using hm
  · simp only [Arrow.comp_right, Arrow.eqToHom_right]
    change j.map (i.map f) = eqToHom (Functor.congr_obj hc w) ≫
      l.map (k.map f) ≫ eqToHom (Functor.congr_obj hc z).symm
    exact Functor.congr_hom hc f

/-- Explicit path-coordinate criterion for surjectivity of the left inclusion
in a groupoid pushout. All the assumptions are local functors, group
homomorphisms, and chosen paths on the two sides and their overlap. -/
theorem pushout_mapEnd_surjective_of_path_coordinates
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) (p : ∀ y : B, x ⟶ y) (hp : p x = 𝟙 x)
    {Q : Type u} [Group Q] (q : End x →* Q) (hq : Function.Surjective q)
    (e : Q →* End (j.obj x)) (he : e.comp q = j.mapEnd x)
    (hoverlap : ∀ (y z : A) (f : y ⟶ z),
      q (p (i.obj y) ≫ i.map f ≫ inv (p (i.obj z))) = 1)
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    Function.Surjective (j.mapEnd x) := by
  have hcompat := basedFunctor_overlap_eq_const i k x p q hoverlap
  let d : D ⥤ VertexTarget.{u,u} Q := (h.desc (basedFunctor x p q).toCatHom
    ((Functor.const C).obj (ULift.up (SingleObj.star Q))).toCatHom
    (Cat.ext hcompat)).toFunctor
  have hdj : j ⋙ d = basedFunctor x p q :=
    congrArg Cat.Hom.toFunctor (h.inl_desc (basedFunctor x p q).toCatHom
      ((Functor.const C).obj (ULift.up (SingleObj.star Q))).toCatHom (Cat.ext hcompat))
  have hdl : l ⋙ d = (Functor.const C).obj (ULift.up (SingleObj.star Q)) :=
    congrArg Cat.Hom.toFunctor (h.inr_desc (basedFunctor x p q).toCatHom
      ((Functor.const C).obj (ULift.up (SingleObj.star Q))).toCatHom (Cat.ext hcompat))
  apply pushout_mapEnd_surjective_of_contraction i k j l h x q hq e he d
    (reconstructionLeft j x p q e he d hdj)
    (reconstructionRight j l x e d hdl c hn)
  · exact reconstruction_overlap i k j l (congrArg Cat.Hom.toFunctor h.w)
      x p q e he d hdj hdl c hn hw
  · change j.map (p x) = 𝟙 (j.obj x)
    rw [hp, j.map_id]

/-- Exactness of the inclusion map is derived from the categorical pushout
and explicit path coordinates. No surjectivity or kernel equality for the
inclusion is assumed. The relator-killing and overlap-coordinate hypotheses
must be established from the disk/annulus geometry before applying this lemma. -/
theorem pushout_exact_of_path_coordinates
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) (p : ∀ y : B, x ⟶ y) (hp : p x = 𝟙 x)
    {ι : Type u} (r : ι → End x) (hr : ∀ a, j.mapEnd x (r a) = 1)
    (hoverlap : ∀ (y z : A) (f : y ⟶ z),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))
        (p (i.obj y) ≫ i.map f ≫ inv (p (i.obj z))) = 1)
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    Function.Surjective (j.mapEnd x) ∧
      (j.mapEnd x).ker = Subgroup.normalClosure (Set.range r) := by
  constructor
  · exact pushout_mapEnd_surjective_of_path_coordinates i k j l h x p hp
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (liftNormalClosure r (j.mapEnd x) hr)
      (liftNormalClosure_comp_mk r (j.mapEnd x) hr) hoverlap c hn hw
  · apply le_antisymm
    · exact pushout_kernel_le_normalClosure i k j l h x p hp r hoverlap
    · exact (normalClosure_range_le_ker_iff r (j.mapEnd x)).mpr hr

/-- The path-coordinate criterion yields a quotient isomorphism that commutes
with the actual inclusion on every loop. -/
theorem pushout_quotient_equiv_of_path_coordinates
    {A B C D : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (x : B) (p : ∀ y : B, x ⟶ y) (hp : p x = 𝟙 x)
    {ι : Type u} (r : ι → End x) (hr : ∀ a, j.mapEnd x (r a) = 1)
    (hoverlap : ∀ (y z : A) (f : y ⟶ z),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range r))
        (p (i.obj y) ≫ i.map f ≫ inv (p (i.obj z))) = 1)
    (c : ∀ y : C, j.obj x ⟶ l.obj y)
    (hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z)
    (hw : ∀ w : A, HEq (j.map (p (i.obj w))) (c (k.obj w))) :
    ∃ E : End x ⧸ Subgroup.normalClosure (Set.range r) ≃* End (j.obj x),
      ∀ g : End x, E (QuotientGroup.mk' (Subgroup.normalClosure (Set.range r)) g) =
        j.mapEnd x g := by
  obtain ⟨hsurj, hker⟩ := pushout_exact_of_path_coordinates i k j l h x p hp r hr
    hoverlap c hn hw
  exact ⟨quotientNormalClosureEquiv r (j.mapEnd x) hsurj hker, fun _ => rfl⟩

/-- Chosen paths from a vertex can always be normalized at that vertex. -/
noncomputable def normalizedPaths
    {B : Type u} [Groupoid.{u} B] (x : B) (hB : ∀ y : B, Nonempty (x ⟶ y)) :
    ∀ y : B, x ⟶ y := by
  classical
  exact fun y => if h : x = y then eqToHom h else Classical.choice (hB y)

@[simp] theorem normalizedPaths_self
    {B : Type u} [Groupoid.{u} B] (x : B) (hB : ∀ y : B, Nonempty (x ⟶ y)) :
    normalizedPaths x hB x = 𝟙 x := by
  classical
  simp [normalizedPaths]

/-- Extend prescribed anchor-to-overlap paths to all left-hand objects. The
object embedding prevents different overlap prescriptions from colliding. -/
noncomputable def overlapCoordinates
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (x : B) (index : A → I) (anchor : I → A)
    (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) (fallback : ∀ y : B, x ⟶ y) :
    ∀ y : B, x ⟶ y := by
  classical
  exact fun y => if h : ∃ w : A, i.obj w = y then
    p (index (Classical.choose h)) ≫ i.map (q (Classical.choose h)) ≫
      eqToHom (Classical.choose_spec h)
    else fallback y

theorem overlapCoordinates_on_overlap
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (hi : Function.Injective i.obj) (x : B)
    (index : A → I) (anchor : I → A) (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) (fallback : ∀ y : B, x ⟶ y) (w : A) :
    overlapCoordinates i x index anchor q p fallback (i.obj w) =
      p (index w) ≫ i.map (q w) := by
  classical
  let h : ∃ z : A, i.obj z = i.obj w := ⟨w, rfl⟩
  have hz : Classical.choose h = w := hi (Classical.choose_spec h)
  simp only [overlapCoordinates, dite_eq_left h]
  have ht (a b : A) (hab : a = b) :
      (p (index a) ≫ i.map (q a)) ≫ eqToHom (congrArg i.obj hab) =
        p (index b) ≫ i.map (q b) := by
    cases hab
    simp
  simpa only [Category.assoc] using ht (Classical.choose h) w hz

/-- A connected left-hand groupoid and an overlap object embedding provide
normalized coordinates extending all prescribed overlap paths. The base vertex
is assumed outside the overlap, as in the standard cell-attachment cover. -/
theorem exists_overlapCoordinates
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (hi : Function.Injective i.obj) (x : B)
    (hx : ∀ w : A, i.obj w ≠ x) (hB : ∀ y : B, Nonempty (x ⟶ y))
    (index : A → I) (anchor : I → A) (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) :
    ∃ s : ∀ y : B, x ⟶ y, s x = 𝟙 x ∧
      ∀ w : A, s (i.obj w) = p (index w) ≫ i.map (q w) := by
  classical
  refine ⟨overlapCoordinates i x index anchor q p (normalizedPaths x hB), ?_, ?_⟩
  · have hnot : ¬ ∃ w : A, i.obj w = x := by
      rintro ⟨w, hw⟩
      exact hx w hw
    simp [overlapCoordinates, hnot]
  · exact overlapCoordinates_on_overlap i hi x index anchor q p _

/-- Trivial vertex groups in a groupoid imply uniqueness of every morphism
between fixed endpoints; no connectedness between distinct components is needed. -/
theorem hom_subsingleton_of_end_subsingleton
    {C : Type u} [Groupoid.{u} C] (hC : ∀ y : C, Subsingleton (End y)) (x y : C) :
    Subsingleton (x ⟶ y) := by
  constructor
  intro f g
  have hfg : f ≫ inv g = 𝟙 x := (hC x).elim _ _
  have hh := congrArg (fun t : End x => t ≫ g) hfg
  simpa [Category.assoc] using hh

/-- Transporting a dependent family of paths along an equality of anchor
indices gives the other chosen path. -/
theorem dependent_path_congr
    {I C : Type u} [Category.{u} C] (anchor : I → C) (x : C)
    (p : ∀ a : I, x ⟶ anchor a) {a b : I} (h : a = b) :
    p a ≫ eqToHom (congrArg anchor h) = p b := by
  cases h
  simp

/-- Paths from a common vertex to each thin component's anchor, followed by
paths inside that component, give natural right-hand coordinates. -/
noncomputable def rightCoordinates
    {I C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (l : C ⥤ D) (x : D) (index : C → I) (anchor : I → C)
    (s : ∀ y : C, anchor (index y) ⟶ y) (p : ∀ a : I, x ⟶ l.obj (anchor a)) :
    ∀ y : C, x ⟶ l.obj y := fun y => p (index y) ≫ l.map (s y)

theorem rightCoordinates_natural
    {I C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (l : C ⥤ D) (x : D) (index : C → I) (anchor : I → C)
    (s : ∀ y : C, anchor (index y) ⟶ y) (p : ∀ a : I, x ⟶ l.obj (anchor a))
    (hC : ∀ y : C, Subsingleton (End y))
    (hindex : ∀ (y z : C) (_f : y ⟶ z), index y = index z)
    (y z : C) (f : y ⟶ z) :
    rightCoordinates l x index anchor s p y ≫ l.map f =
      rightCoordinates l x index anchor s p z := by
  have h := hindex y z f
  have hs : s y ≫ f = eqToHom (congrArg anchor h) ≫ s z :=
    (hom_subsingleton_of_end_subsingleton hC _ _).elim _ _
  change (p (index y) ≫ l.map (s y)) ≫ l.map f = p (index z) ≫ l.map (s z)
  rw [Category.assoc, ← l.map_comp, hs, l.map_comp, eqToHom_map l, ← Category.assoc]
  rw [dependent_path_congr (fun a => l.obj (anchor a)) x p h]

/-- An anchor path on the left becomes an anchor path for its right-hand
component by commutativity of the square. -/
noncomputable def mappedAnchorPaths
    {A B C D I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (hc : i ⋙ j = k ⋙ l) (x : B) (anchor : I → A)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) :
    ∀ a : I, j.obj x ⟶ l.obj (k.obj (anchor a)) :=
  fun a => j.map (p a) ≫ eqToHom (Functor.congr_obj hc (anchor a))

/-- The left and right anchor-coordinate constructions agree on the overlap.
Thinness of a right-hand component identifies the two paths from its anchor. -/
theorem rightCoordinates_match_overlap
    {A B C D I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (hc : i ⋙ j = k ⋙ l) (x : B) (indexA : A → I) (indexC : C → I)
    (anchor : I → A) (q : ∀ w : A, anchor (indexA w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a))
    (s : ∀ y : C, k.obj (anchor (indexC y)) ⟶ y)
    (hC : ∀ y : C, Subsingleton (End y))
    (hindex : ∀ w : A, indexC (k.obj w) = indexA w) (w : A) :
    HEq (j.map (p (indexA w) ≫ i.map (q w)))
      (rightCoordinates l (j.obj x) indexC (fun a => k.obj (anchor a)) s
        (mappedAnchorPaths i k j l hc x anchor p) (k.obj w)) := by
  let r := mappedAnchorPaths i k j l hc x anchor p
  have hi : indexA w = indexC (k.obj w) := (hindex w).symm
  have hs : k.map (q w) =
      eqToHom (congrArg (fun a => k.obj (anchor a)) hi) ≫ s (k.obj w) :=
    (hom_subsingleton_of_end_subsingleton hC _ _).elim _ _
  have hr : r (indexA w) ≫ l.map
      (eqToHom (congrArg (fun a => k.obj (anchor a)) hi)) = r (indexC (k.obj w)) := by
    rw [eqToHom_map]
    exact dependent_path_congr (fun a => l.obj (k.obj (anchor a))) (j.obj x) r hi
  apply (conj_eqToHom_iff_heq _ _ rfl (Functor.congr_obj hc w)).mp
  simp only [eqToHom_refl, Category.id_comp]
  change j.map (p (indexA w) ≫ i.map (q w)) =
    (r (indexC (k.obj w)) ≫ l.map (s (k.obj w))) ≫
      eqToHom (Functor.congr_obj hc w).symm
  calc
    j.map (p (indexA w) ≫ i.map (q w)) =
        r (indexA w) ≫ l.map (k.map (q w)) ≫
          eqToHom (Functor.congr_obj hc w).symm := by
      have hm := Functor.congr_hom hc (q w)
      change j.map (i.map (q w)) =
        eqToHom (Functor.congr_obj hc (anchor (indexA w))) ≫
          l.map (k.map (q w)) ≫ eqToHom (Functor.congr_obj hc w).symm at hm
      rw [j.map_comp, hm]
      simp [r, mappedAnchorPaths, Category.assoc]
    _ = (r (indexC (k.obj w)) ≫ l.map (s (k.obj w))) ≫
        eqToHom (Functor.congr_obj hc w).symm := by
      rw [hs, l.map_comp]
      simp only [← Category.assoc]
      rw [hr]

/-- Coordinates prescribed componentwise on the overlap kill every overlap
arrow as soon as they kill each component's transported cyclic generator. -/
theorem overlapCoordinates_eq_one_of_cyclic
    {A B I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    (i : A ⥤ B) (x : B) (index : A → I) (anchor : I → A)
    (q : ∀ w : A, anchor (index w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a)) (s : ∀ y : B, x ⟶ y)
    (hs : ∀ w : A, s (i.obj w) = p (index w) ≫ i.map (q w))
    (hindex : ∀ (y z : A) (_f : y ⟶ z), index y = index z)
    (r : ∀ a : I, End (anchor a))
    (hcyc : ∀ (a : I) (g : End (anchor a)), ∃ n : ℤ, g = r a ^ n)
    {G : Type u} [Group G] (F : End x →* G)
    (hr : ∀ a, F (overlapLoop i x (anchor a) (p a) (r a)) = 1)
    (y z : A) (f : y ⟶ z) :
    F (s (i.obj y) ≫ i.map f ≫ inv (s (i.obj z))) = 1 := by
  have h := hindex y z f
  let t : anchor (index y) ⟶ z := eqToHom (congrArg anchor h) ≫ q z
  have ht : p (index z) ≫ i.map (q z) = p (index y) ≫ i.map t := by
    dsimp [t]
    rw [i.map_comp, ← Category.assoc, eqToHom_map]
    rw [dependent_path_congr (fun a => i.obj (anchor a)) x p h]
  rw [hs y, hs z, ht]
  exact overlap_coordinate_eq_one_of_cyclic i x (anchor (index y)) y z
    (p (index y)) (q y) t f (r (index y)) (hcyc (index y)) F (hr (index y))

/-- The algebraic bridge from a categorical groupoid pushout to the quotient
of the actual left vertex group. Connectedness, overlap object embedding,
component paths, thin right-hand vertex groups, and cyclic overlap vertex groups
supply the path coordinates; neither surjectivity nor kernel exactness is assumed.

Applying this to a two-cell attachment still requires the genuine topological
open-cover pushout and proofs of all listed local groupoid hypotheses. -/
theorem pushout_vertex_quotient_of_component_data
    {A B C D I : Type u} [Groupoid.{u} A] [Groupoid.{u} B]
    [Groupoid.{u} C] [Groupoid.{u} D]
    (i : A ⥤ B) (k : A ⥤ C) (j : B ⥤ D) (l : C ⥤ D)
    (h : IsPushout i.toCatHom k.toCatHom j.toCatHom l.toCatHom)
    (hi : Function.Injective i.obj) (x : B) (hx : ∀ w : A, i.obj w ≠ x)
    (hB : ∀ y : B, Nonempty (x ⟶ y))
    (indexA : A → I) (indexC : C → I) (anchor : I → A)
    (q : ∀ w : A, anchor (indexA w) ⟶ w)
    (p : ∀ a : I, x ⟶ i.obj (anchor a))
    (s : ∀ y : C, k.obj (anchor (indexC y)) ⟶ y)
    (hC : ∀ y : C, Subsingleton (End y))
    (hindexC : ∀ (y z : C) (_f : y ⟶ z), indexC y = indexC z)
    (hindex : ∀ w : A, indexC (k.obj w) = indexA w)
    (r : ∀ a : I, End (anchor a))
    (hcyc : ∀ (a : I) (g : End (anchor a)), ∃ n : ℤ, g = r a ^ n) :
    let R : I → End x := fun a => overlapLoop i x (anchor a) (p a) (r a)
    Function.Surjective (j.mapEnd x) ∧
      (j.mapEnd x).ker = Subgroup.normalClosure (Set.range R) ∧
      ∃ E : End x ⧸ Subgroup.normalClosure (Set.range R) ≃* End (j.obj x),
        ∀ g : End x, E (QuotientGroup.mk' (Subgroup.normalClosure (Set.range R)) g) =
          j.mapEnd x g := by
  intro R
  have hc : i ⋙ j = k ⋙ l := congrArg Cat.Hom.toFunctor h.w
  obtain ⟨pB, hpB, hpres⟩ := exists_overlapCoordinates i hi x hx hB indexA anchor q p
  let c := rightCoordinates l (j.obj x) indexC (fun a => k.obj (anchor a)) s
    (mappedAnchorPaths i k j l hc x anchor p)
  have hn : ∀ (y z : C) (f : y ⟶ z), c y ≫ l.map f = c z :=
    rightCoordinates_natural l (j.obj x) indexC (fun a => k.obj (anchor a)) s
      (mappedAnchorPaths i k j l hc x anchor p) hC hindexC
  have hw : ∀ w : A, HEq (j.map (pB (i.obj w))) (c (k.obj w)) := by
    intro w
    rw [hpres w]
    exact rightCoordinates_match_overlap i k j l hc x indexA indexC anchor q p s hC hindex w
  have hindexA : ∀ (y z : A) (_f : y ⟶ z), indexA y = indexA z := by
    intro y z f
    exact (hindex y).symm.trans ((hindexC _ _ (k.map f)).trans (hindex z))
  have hr : ∀ a, j.mapEnd x (R a) = 1 := by
    intro a
    apply map_overlapLoop_eq_one i k j l hc x (anchor a) (p a) (r a)
    exact (hC (k.obj (anchor a))).elim _ _
  have hoverlap : ∀ (y z : A) (f : y ⟶ z),
      QuotientGroup.mk' (Subgroup.normalClosure (Set.range R))
        (pB (i.obj y) ≫ i.map f ≫ inv (pB (i.obj z))) = 1 := by
    apply overlapCoordinates_eq_one_of_cyclic i x indexA anchor q p pB hpres hindexA r hcyc
    intro a
    change (R a : End x ⧸ Subgroup.normalClosure (Set.range R)) = 1
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.subset_normalClosure (Set.mem_range_self a))
  obtain ⟨hsurj, hker⟩ := pushout_exact_of_path_coordinates i k j l h x pB hpB R hr
    hoverlap c hn hw
  exact ⟨hsurj, hker,
    quotientNormalClosureEquiv R (j.mapEnd x) hsurj hker, fun _ => rfl⟩

end ArrowDescent

end CellAttachment
