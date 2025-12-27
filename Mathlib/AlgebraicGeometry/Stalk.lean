import VerifiedAgora.tagger
/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Fangming Li
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Stalks of a Scheme

## Main definitions and results

- `AlgebraicGeometry.Scheme.fromSpecStalk`: The canonical morphism `Spec 𝒪_{X, x} ⟶ X`.
- `AlgebraicGeometry.Scheme.range_fromSpecStalk`: The range of the map `Spec 𝒪_{X, x} ⟶ X` is
  exactly the `y`s that specialize to `x`.
- `AlgebraicGeometry.SpecToEquivOfLocalRing`:
  Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
  `(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

section fromSpecStalk

/--
A morphism from `Spec(O_x)` to `X`, which is defined with the help of an affine open
neighborhood `U` of `x`.
-/
noncomputable def IsAffineOpen.fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

/--
The morphism from `Spec(O_x)` to `X` given by `IsAffineOpen.fromSpec` does not depend on the affine
open neighborhood of `x` we choose.
-/
theorem IsAffineOpen.fromSpecStalk_eq (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X) (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op]
    erw [← Scheme.Spec_map (X.presheaf.map _).op, ← Scheme.Spec_map (X.presheaf.germ _ x h₂).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res, Scheme.Spec_map,
      Quiver.Hom.unop_op]
  · delta fromSpecStalk
    rw [← hV.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_right).op]
    erw [← Scheme.Spec_map (X.presheaf.map _).op, ← Scheme.Spec_map (X.presheaf.germ _ x h₂).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res, Scheme.Spec_map,
      Quiver.Hom.unop_op]

/--
If `x` is a point of `X`, this is the canonical morphism from `Spec(O_x)` to `X`.
-/
noncomputable def Scheme.fromSpecStalk (X : Scheme) (x : X) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  (isAffineOpen_opensRange (X.affineOpenCover.map x)).fromSpecStalk (X.affineOpenCover.covers x)

@[simps over] noncomputable
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).Over X := ⟨X.fromSpecStalk x⟩

@[simps! over] noncomputable
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).CanonicallyOver X where

@[simp]
theorem IsAffineOpen.fromSpecStalk_eq_fromSpecStalk {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x := fromSpecStalk_eq ..

instance IsAffineOpen.fromSpecStalk_isPreimmersion {X : Scheme.{u}} {U : Opens X}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) : IsPreimmersion (hU.fromSpecStalk hx) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  haveI : IsPreimmersion (Spec.map (X.presheaf.germ U x hx)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    IsPreimmersion.of_isLocalization (R := Γ(X, U)) (S := X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  apply IsPreimmersion.comp

instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecStalk x) :=
  IsAffineOpen.fromSpecStalk_isPreimmersion _ _ _

lemma IsAffineOpen.fromSpecStalk_closedPoint {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    (hU.fromSpecStalk hxU).base (closedPoint (X.presheaf.stalk x)) = x := by
  rw [IsAffineOpen.fromSpecStalk, Scheme.comp_base_apply]
  rw [← hU.primeIdealOf_eq_map_closedPoint ⟨x, hxU⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩]

namespace Scheme

@[target] lemma IsAffineOpen.fromSpecStalk_closedPoint {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    (hU.fromSpecStalk hxU).base (closedPoint (X.presheaf.stalk x)) = x := by
  sorry


@[target] lemma fromSpecStalk_app {x : X} (hxU : x ∈ U) :
    (X.fromSpecStalk x).app U =
      X.presheaf.germ U x hxU ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
  sorry


lemma fromSpecStalk_appTop {x : X} :
    (X.fromSpecStalk x).appTop =
      X.presheaf.germ ⊤ x trivial ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op :=
  fromSpecStalk_app ..

@[target] lemma Spec_map_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x := by
  sorry


instance {x y : X} (h : x ⤳ y) : (Spec.map (X.presheaf.stalkSpecializes h)).IsOver X where

@[target] lemma Spec_map_stalkMap_fromSpecStalk {x} :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecStalk x ≫ f := by
  sorry


instance [X.Over Y] {x} : Spec.map ((X ↘ Y).stalkMap x) |>.IsOver Y where

@[target] lemma Spec_fromSpecStalk (R : CommRingCat) (x) :
    (Spec R).fromSpecStalk x =
      Spec.map ((ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) := by
  sorry

/-- A variant of `Spec_fromSpecStalk` that breaks abstraction boundaries. -/
lemma Spec_fromSpecStalk' (R : CommRingCat) (x) :
    (Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _) :=
  Spec_fromSpecStalk _ _

@[target] lemma range_fromSpecStalk {x : X} :
    Set.range (X.fromSpecStalk x).base = { y | y ⤳ x } := by
  sorry


/-- The canonical map `Spec 𝒪_{X, x} ⟶ U` given `x ∈ U ⊆ X`. -/
noncomputable
def Opens.fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ U :=
  Spec.map (inv (U.ι.stalkMap ⟨x, hxU⟩)) ≫ U.toScheme.fromSpecStalk ⟨x, hxU⟩

@[reassoc (attr := simp)]
lemma Opens.fromSpecStalkOfMem_ι {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.ι = X.fromSpecStalk x := by
  simp only [Opens.fromSpecStalkOfMem, Spec.map_inv, Category.assoc, IsIso.inv_comp_eq]
  exact (Scheme.Spec_map_stalkMap_fromSpecStalk U.ι (x := ⟨x, hxU⟩)).symm

instance {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    (U.fromSpecStalkOfMem x hxU).IsOver X where

@[reassoc]
lemma fromSpecStalk_toSpecΓ (X : Scheme.{u}) (x : X) :
    X.fromSpecStalk x ≫ X.toSpecΓ = Spec.map (X.presheaf.germ ⊤ x trivial) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    Scheme.fromSpecStalk_appTop]
  simp

@[reassoc (attr := simp)]
lemma Opens.fromSpecStalkOfMem_toSpecΓ {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.toSpecΓ = Spec.map (X.presheaf.germ U x hxU) := by
  rw [fromSpecStalkOfMem, Opens.toSpecΓ, Category.assoc, fromSpecStalk_toSpecΓ_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  rw [IsIso.comp_inv_eq, Iso.inv_comp_eq]
  erw [stalkMap_germ U.ι U ⟨x, hxU⟩]
  rw [Opens.ι_app, Opens.topIso_hom, ← Functor.map_comp_assoc]
  exact (U.toScheme.presheaf.germ_res (homOfLE le_top) ⟨x, hxU⟩ (U := U.ι ⁻¹ᵁ U) hxU).symm

end Scheme

end fromSpecStalk

variable (R : CommRingCat.{u}) [IsLocalRing R]

section stalkClosedPointIso

/-- For a local ring `(R, 𝔪)`,
this is the isomorphism between the stalk of `Spec R` at `𝔪` and `R`. -/
/-- For a local ring `(R, 𝔪)`,
this is the isomorphism between the stalk of `Spec R` at `𝔪` and `R`. -/
noncomputable
def stalkClosedPointIso :
    (Spec R).presheaf.stalk (closedPoint R) ≅ R := by sorry


@[target] lemma stalkClosedPointIso_inv :
    (stalkClosedPointIso R).inv = StructureSheaf.toStalk R _ := by
  sorry


lemma ΓSpecIso_hom_stalkClosedPointIso_inv :
    (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv =
      (Spec R).presheaf.germ ⊤ (closedPoint _) trivial := by
  rw [stalkClosedPointIso_inv, ← Iso.eq_inv_comp]
  rfl

@[target] lemma germ_stalkClosedPointIso_hom :
    (Spec R).presheaf.germ ⊤ (closedPoint _) trivial ≫ (stalkClosedPointIso R).hom =
      (Scheme.ΓSpecIso R).hom := by
  sorry


@[target] lemma Spec_stalkClosedPointIso :
    Spec.map (stalkClosedPointIso R).inv = (Spec R).fromSpecStalk (closedPoint R) := by
  sorry


end stalkClosedPointIso

section stalkClosedPointTo

variable {R} (f : Spec R ⟶ X)

namespace Scheme

/--
Given a local ring `(R, 𝔪)` and a morphism `f : Spec R ⟶ X`,
they induce a (local) ring homomorphism `φ : 𝒪_{X, f 𝔪} ⟶ R`.

This is inverse to `φ ↦ Spec.map φ ≫ X.fromSpecStalk (f 𝔪)`. See `SpecToEquivOfLocalRing`.
-/
/--
Given a local ring `(R, 𝔪)` and a morphism `f : Spec R ⟶ X`,
they induce a (local) ring homomorphism `φ : 𝒪_{X, f 𝔪} ⟶ R`.

This is inverse to `φ ↦ Spec.map φ ≫ X.fromSpecStalk (f 𝔪)`. See `SpecToEquivOfLocalRing`.
-/
noncomputable
def stalkClosedPointTo :
    X.presheaf.stalk (f.base (closedPoint R)) ⟶ R := by sorry


instance isLocalHom_stalkClosedPointTo :
    IsLocalHom (stalkClosedPointTo f).hom :=
  inferInstanceAs <| IsLocalHom (f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom).hom

/-- Copy of `isLocalHom_stalkClosedPointTo` which unbundles the comm ring.

Useful for use in combination with `CommRingCat.of K` for a field `K`.
-/
instance isLocalHom_stalkClosedPointTo' {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ X) :
    IsLocalHom (stalkClosedPointTo f).hom :=
  isLocalHom_stalkClosedPointTo f

@[target] lemma preimage_eq_top_of_closedPoint_mem
    {U : Opens X} (hU : f.base (closedPoint R) ∈ U) : f ⁻¹ᵁ U = ⊤ := by sorry


lemma stalkClosedPointTo_comp (g : X ⟶ Y) :
    stalkClosedPointTo (f ≫ g) = g.stalkMap _ ≫ stalkClosedPointTo f := by
  rw [stalkClosedPointTo, Scheme.stalkMap_comp]
  exact Category.assoc _ _ _

lemma germ_stalkClosedPointTo_Spec {R S : CommRingCat} [IsLocalRing S] (φ : R ⟶ S):
    (Spec R).presheaf.germ ⊤ _ trivial ≫ stalkClosedPointTo (Spec.map φ) =
      (ΓSpecIso R).hom ≫ φ := by
  rw [stalkClosedPointTo, Scheme.stalkMap_germ_assoc, ← Iso.inv_comp_eq,
    ← ΓSpecIso_inv_naturality_assoc]
  simp_rw [Opens.map_top]
  rw [germ_stalkClosedPointIso_hom, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
lemma germ_stalkClosedPointTo (U : Opens X) (hU : f.base (closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo f = f.app U ≫
      ((Spec R).presheaf.mapIso (eqToIso (preimage_eq_top_of_closedPoint_mem f hU).symm).op ≪≫
        ΓSpecIso R).hom := by
  rw [stalkClosedPointTo, Scheme.stalkMap_germ_assoc, Iso.trans_hom]
  congr 1
  rw [← Iso.eq_comp_inv, Category.assoc, ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [TopCat.Presheaf.pushforward_obj_obj, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    TopCat.Presheaf.germ_res]

@[target] lemma germ_stalkClosedPointTo_Spec_fromSpecStalk
    {x : X} (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom] (U : Opens X) (hU) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x) =
      X.presheaf.germ U x (by sorry


@[target] lemma stalkClosedPointTo_fromSpecStalk (x : X) :
    stalkClosedPointTo (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (by sorry


@[reassoc]
lemma Spec_stalkClosedPointTo_fromSpecStalk :
    Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStalk _ = f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := (isBasis_affine_open X).exists_subset_of_mem_open
    (Set.mem_univ (f.base (closedPoint R))) isOpen_univ
  have := IsAffineOpen.Spec_map_appLE_fromSpec f hU (isAffineOpen_top _)
    (preimage_eq_top_of_closedPoint_mem f hxU).ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, isoSpec_Spec_hom] at this
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc,
    germ_stalkClosedPointTo]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    Hom.app_eq_appLE, Hom.appLE_map_assoc, Spec.map_comp_assoc]

end Scheme

end stalkClosedPointTo

variable {R}

omit [IsLocalRing R] in
/-- useful lemma for applications of `SpecToEquivOfLocalRing` -/
omit [IsLocalRing R] in
/-- useful lemma for applications of `SpecToEquivOfLocalRing` -/
@[target] lemma SpecToEquivOfLocalRing_eq_iff
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }} :
    f₁ = f₂ ↔ ∃ h₁ : f₁.1 = f₂.1, f₁.2.1 =
      (X.presheaf.stalkCongr (by sorry


variable (X R)

/--
Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
`(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/
/--
Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
`(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/
@[simps]
noncomputable
def SpecToEquivOfLocalRing :
    (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom } where
  toFun f := ⟨f.base (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk
  right_inv xf := by
    sorry


end AlgebraicGeometry
