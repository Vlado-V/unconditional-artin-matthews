module

public import ArtinMatthews.SourceKPAdeleCoordinates
public import Mathlib.NumberTheory.NumberField.AdeleRing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual idele absolute norm. Its finite product has genuine
finite support, and its infinite factors carry the normalized place
multiplicities. The number-field product formula makes it one on
actual principal ideles. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPAdeleInfiniteProjection : 𝔸[K] →+* InfiniteAdeleRing K :=
  RingHom.fst (InfiniteAdeleRing K) 𝔸ᶠ[K]

def sourceKPAdeleFiniteProjection : 𝔸[K] →+* 𝔸ᶠ[K] :=
  RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K]

def sourceKPIdeleInfiniteUnit : IdeleGroup (𝓞 K) K →* (InfiniteAdeleRing K)ˣ :=
  Units.map (sourceKPAdeleInfiniteProjection K).toMonoidHom

def sourceKPIdeleFiniteUnit : IdeleGroup (𝓞 K) K →* 𝔸ᶠ[K]ˣ :=
  Units.map (sourceKPAdeleFiniteProjection K).toMonoidHom

theorem sourceKPFiniteUnit_norm_mul (x y : 𝔸ᶠ[K]ˣ) :
    ‖((x * y : 𝔸ᶠ[K]ˣ) : 𝔸ᶠ[K])‖ = ‖(x : 𝔸ᶠ[K])‖ * ‖(y : 𝔸ᶠ[K])‖ := by
  rw [FiniteAdeleRing.norm_eq_finprod_of_unit, FiniteAdeleRing.norm_eq_finprod_of_unit,
    FiniteAdeleRing.norm_eq_finprod_of_unit]
  calc
    _ = ∏ᶠ P : HeightOneSpectrum (𝓞 K), ‖(x : 𝔸ᶠ[K]) P‖ * ‖(y : 𝔸ᶠ[K]) P‖ := by
      apply finprod_congr
      intro P
      exact norm_mul _ _
    _ = _ := finprod_mul_distrib (FiniteAdeleRing.hasFiniteMulSupport_norm x) (FiniteAdeleRing.hasFiniteMulSupport_norm y)

theorem sourceKPFiniteUnit_norm_pos (x : 𝔸ᶠ[K]ˣ) : 0 < ‖(x : 𝔸ᶠ[K])‖ := by
  rw [FiniteAdeleRing.norm_eq_finprod_of_unit, finprod_eq_prod _ (FiniteAdeleRing.hasFiniteMulSupport_norm x)]
  apply Finset.prod_pos
  intro P _
  exact norm_pos_iff.mpr (Units.map (sourceKPAdeleEval K P).toMonoidHom x).ne_zero

theorem sourceKPInfiniteUnit_norm_mul (x y : (InfiniteAdeleRing K)ˣ) :
    ‖((x * y : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ =
      ‖(x : InfiniteAdeleRing K)‖ * ‖(y : InfiniteAdeleRing K)‖ := by
  rw [InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_def, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _
  change ‖(x : InfiniteAdeleRing K) w * (y : InfiniteAdeleRing K) w‖ ^ w.mult = _
  rw [norm_mul, mul_pow]

theorem sourceKPInfiniteUnit_norm_pos (x : (InfiniteAdeleRing K)ˣ) : 0 < ‖(x : InfiniteAdeleRing K)‖ := by
  rw [InfiniteAdeleRing.norm_def]
  apply Finset.prod_pos
  intro w _
  apply pow_pos (norm_pos_iff.mpr ?_)
  intro h
  have he := congrArg (fun a : InfiniteAdeleRing K => a w) x.val_inv
  change (x : InfiniteAdeleRing K) w * ((x⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = 1 at he
  rw [h, zero_mul] at he
  exact zero_ne_one he

def sourceKPIdeleAbsoluteNorm : IdeleGroup (𝓞 K) K →* ℝ where
  toFun x := ‖(sourceKPIdeleInfiniteUnit K x : InfiniteAdeleRing K)‖ * ‖(sourceKPIdeleFiniteUnit K x : 𝔸ᶠ[K])‖
  map_one' := by
    have hI : ‖(1 : InfiniteAdeleRing K)‖ = 1 := by
      rw [InfiniteAdeleRing.norm_def]
      change (∏ w : InfinitePlace K, ‖(1 : w.Completion)‖ ^ w.mult) = 1
      simp
    have hF : ‖(1 : 𝔸ᶠ[K])‖ = 1 := by
      have h := FiniteAdeleRing.norm_eq_finprod_of_unit (1 : 𝔸ᶠ[K]ˣ)
      change ‖(1 : 𝔸ᶠ[K])‖ = ∏ᶠ P : HeightOneSpectrum (𝓞 K), ‖(1 : P.adicCompletion K)‖ at h
      rw [h]
      simp
    rw [map_one, map_one]
    change ‖(1 : InfiniteAdeleRing K)‖ * ‖(1 : 𝔸ᶠ[K])‖ = 1
    rw [hI, hF, one_mul]
  map_mul' x y := by
    rw [map_mul, map_mul, sourceKPInfiniteUnit_norm_mul, sourceKPFiniteUnit_norm_mul]
    ac_rfl

theorem sourceKPIdeleAbsoluteNorm_pos (x : IdeleGroup (𝓞 K) K) : 0 < sourceKPIdeleAbsoluteNorm K x :=
  mul_pos (sourceKPInfiniteUnit_norm_pos K _) (sourceKPFiniteUnit_norm_pos K _)

theorem sourceKPIdeleAbsoluteNorm_principal (x : Kˣ) :
    sourceKPIdeleAbsoluteNorm K (IdeleGroup.unitEmbedding (𝓞 K) K x) = 1 := by
  change ‖algebraMap K (InfiniteAdeleRing K) (x : K)‖ * ‖(FiniteAdeleRing.unitEmbedding (𝓞 K) K x : 𝔸ᶠ[K])‖ = 1
  rw [InfiniteAdeleRing.coe_norm_eq_abs_norm, FiniteAdeleRing.unitEmbedding_norm_apply_eq_finprod_finitePlace,
    ← InfinitePlace.prod_eq_abs_norm]
  exact NumberField.prod_abs_eq_one x.ne_zero

end
end ArtinMatthews
