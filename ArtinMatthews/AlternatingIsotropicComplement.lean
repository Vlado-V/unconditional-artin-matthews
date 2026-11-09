module

public import ArtinMatthews.AlternatingTriangularComplement
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.FieldTheory.Finiteness


set_option backward.privateInPublic true
@[expose] public section

/-! Isotropic complements without division by two. The arithmetic application
must supply its actual alternating nondegenerate form and isotropic subspace. -/

namespace ArtinMatthews

noncomputable section

open LinearMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_bilin_alternating_correction [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) :
    ∃ C : LinearMap.BilinForm K V, ∀ x y, C x y - C y x = -B x y := by
  classical
  let b := Module.finBasis K V
  let A := LinearMap.BilinForm.toMatrix b B
  let C := Matrix.toBilin b (-alternatingUpper A)
  have hEntry (i j) : C (b i) (b j) = -alternatingUpper A i j := by
    have h : (LinearMap.BilinForm.toMatrix b) C = -alternatingUpper A :=
      (LinearMap.BilinForm.toMatrix b).apply_symm_apply (-alternatingUpper A)
    simpa only [LinearMap.BilinForm.toMatrix_apply, Matrix.neg_apply] using
      congrArg (fun M => M i j) h
  have hC : C - LinearMap.flip C = -B := by
    apply LinearMap.ext_basis b b
    intro i j
    change C (b i) (b j) - C (b j) (b i) = -B (b i) (b j)
    rw [hEntry, hEntry]
    have hdiag : B (b i) (b i) = 0 := hAlt.self_eq_zero _
    have hskew : B (b j) (b i) = -B (b i) (b j) := (hAlt.neg_eq _ _).symm
    rcases lt_trichotomy i j with h | rfl | h
    · simp [A, alternatingUpper, h, not_lt_of_gt h]
    · simp [alternatingUpper, hdiag]
    · simp [A, alternatingUpper, h, not_lt_of_gt h, hskew]
  refine ⟨C, fun x y => ?_⟩
  exact congrArg (fun D : LinearMap.BilinForm K V => D x y) hC

theorem isotropic_complement_pairing_injective
    (B : LinearMap.BilinForm K V) (hNondeg : B.Nondegenerate)
    (E F : Submodule K V) (hEF : IsCompl E F)
    (hIso : ∀ x ∈ E, ∀ y ∈ E, B x y = 0) :
    Function.Injective (B.domRestrict₁₂ E F) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  apply Subtype.ext
  apply hNondeg.1
  intro v
  obtain ⟨e, f, hv, _⟩ := E.existsUnique_add_of_isCompl hEF v
  rw [← hv, map_add, hIso x x.property e e.property, zero_add]
  change (B.domRestrict₁₂ E F) x = 0 at hx
  have hf := congrArg (fun l : Module.Dual K F => l f) hx
  simpa only [LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply] using hf

theorem exists_isotropic_complement_of_finrank [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) (hNondeg : B.Nondegenerate)
    (E : Submodule K V) (hIso : ∀ x ∈ E, ∀ y ∈ E, B x y = 0)
    (hdim : 2 * finrank K E = finrank K V) :
    ∃ F : Submodule K V, IsCompl E F ∧ ∀ x ∈ F, ∀ y ∈ F, B x y = 0 := by
  classical
  obtain ⟨F, hEF⟩ := E.exists_isCompl
  have hdimEF : finrank K E = finrank K F := by
    have h := Submodule.finrank_add_eq_of_isCompl hEF
    omega
  let pair := B.domRestrict₁₂ E F
  have hinj : Function.Injective pair :=
    isotropic_complement_pairing_injective B hNondeg E F hEF hIso
  let e : E ≃ₗ[K] Module.Dual K F := LinearMap.linearEquivOfInjective pair hinj (by
    rw [Subspace.dual_finrank_eq]
    exact hdimEF)
  let BF := B.restrict F
  have hBF : BF.IsAlt := fun x => hAlt.self_eq_zero x
  obtain ⟨C, hC⟩ := exists_bilin_alternating_correction BF hBF
  let T : F →ₗ[K] E := e.symm.toLinearMap.comp C
  let graph : F →ₗ[K] V := E.subtype.comp T + F.subtype
  have hT (x y : F) : B (T x) y = C x y := by
    change (e (e.symm (C x))) y = C x y
    rw [e.apply_symm_apply]
  have hgraph : IsCompl E (LinearMap.range graph) := by
    rw [isCompl_iff]
    constructor
    · rw [Submodule.disjoint_def]
      intro v hv hvg
      obtain ⟨f, rfl⟩ := hvg
      have hfE : (f : V) ∈ E := by
        have h := E.sub_mem hv (T f).property
        simpa [graph] using h
      have hf0 : (f : V) = 0 := Submodule.disjoint_def.mp hEF.disjoint f hfE f.property
      have hf : f = 0 := Subtype.ext hf0
      simp [hf]
    · rw [codisjoint_iff]
      apply top_unique
      intro v _
      obtain ⟨a, f, hv, _⟩ := E.existsUnique_add_of_isCompl hEF v
      rw [Submodule.mem_sup]
      refine ⟨(a : V) - T f, E.sub_mem a.property (T f).property,
        graph f, ⟨f, rfl⟩, ?_⟩
      calc
        (a : V) - T f + graph f = (a : V) + f := by dsimp [graph]; abel
        _ = v := hv
  refine ⟨LinearMap.range graph, hgraph, ?_⟩
  intro x hx y hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  change B ((T u : V) + u) ((T v : V) + v) = 0
  simp only [map_add, LinearMap.add_apply]
  rw [hIso (T u) (T u).property (T v) (T v).property, hT u v,
    ← hAlt.neg_eq (T v) u, hT v u]
  have h := hC u v
  change C u v - C v u = -B u v at h
  linear_combination h

theorem finrank_half_of_card_square [Finite K] [Finite V]
    (E : Submodule K V) (hcard : Nat.card V = (Nat.card E) ^ 2) :
    2 * finrank K E = finrank K V := by
  let : Module.Finite K V := Module.Finite.of_finite
  have hpow : Nat.card K ^ finrank K V =
      (Nat.card K ^ finrank K E) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := V),
      Module.natCard_eq_pow_finrank (K := K) (V := E)] at hcard
    exact hcard
  rw [← pow_mul] at hpow
  have hdim := Nat.pow_right_injective (Finite.one_lt_card (α := K)) hpow
  omega

theorem exists_isotropic_complement_of_card [Finite K] [Finite V]
    (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) (hNondeg : B.Nondegenerate)
    (E : Submodule K V) (hIso : ∀ x ∈ E, ∀ y ∈ E, B x y = 0)
    (hcard : Nat.card V = (Nat.card E) ^ 2) :
    ∃ F : Submodule K V, IsCompl E F ∧ ∀ x ∈ F, ∀ y ∈ F, B x y = 0 := by
  let : Module.Finite K V := Module.Finite.of_finite
  exact exists_isotropic_complement_of_finrank B hAlt hNondeg E hIso
    (finrank_half_of_card_square E hcard)

end

end ArtinMatthews
