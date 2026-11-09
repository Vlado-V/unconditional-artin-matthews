module

public import ArtinMatthews.SourceKPJacquetStableMap
public import ArtinMatthews.SourceKPProjectiveBruhatCells
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Basis.VectorSpace


set_option backward.privateInPublic true
@[expose] public section

/-! Every equivariant linear functional factors through the actual stable
Jacquet map. This uses the two Bruhat cells and the finite upper average. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory Filter
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "B" => sourceLocalBall K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "n₋" => fun t : L => l₀ (sourceGL2Lower t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P
local notation "μ₀" => sourceLocalSelfDual K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
local notation "E₀" => sourceKPJacquetCoordinateIntegrand K hζ P ρ C e
local notation "Tr" => sourceKPJacquetTruncation K hζ P ρ C e

theorem sourceKPJacquetCoordinateIntegral_closed
    (hUpper : ∀ t : L, ∀ v : V, ρ (sourceFiniteKPProjectiveBorelUpper K hζ P t) v = v)
    (f : C) (b : B₀) (R : ℕ) (a : L) (ha : a ∈ B (R : ℤ)) (hψ : ψ₀ (-a) ≠ 1) :
    (∫ t in B (R : ℤ), E₀ f b.val t ∂μ₀) = 0 := by
  have hN (t : L) : f.val.val (n₀ t) = f.val.val 1 := by
    have h := f.val.property (sourceFiniteKPProjectiveBorelUpper K hζ P t) 1
    rwa [mul_one, sourceFiniteKPProjectiveBorelUpper_val, hUpper] at h
  have hb (t : L) : f.val.val (b.val * n₀ t) = f.val.val b.val := by
    rw [f.val.property, hN, ← f.val.property b 1, mul_one]
  have he : E₀ f b.val = fun t => ψ₀ (-t) • e (f.val.val b.val) := by
    funext t
    unfold sourceKPJacquetCoordinateIntegrand
    rw [hb]
  rw [he, integral_smul_const, sourceKPJacquetSelfDual_ball_character_zero K P (R : ℤ) a ha hψ,
    zero_smul]

theorem sourceKPJacquetCoordinateIntegral_open_outside (f : C) (b : B₀) (x : L) (R : ℕ)
    (a : L) (ha : a ∈ B (R : ℤ)) (hψ : ψ₀ (-a) ≠ 1)
    (hOuter : ∀ t ∈ B (R : ℤ),
      f.val.val (w₀ * n₀ (x + t + a)) = f.val.val (w₀ * n₀ (x + t))) :
    (∫ t in B (R : ℤ), E₀ f (b.val * w₀ * n₀ x) t ∂μ₀) = 0 := by
  apply sourceKPJacquetSelfDual_integral_zero_of_phase K P (B (R : ℤ))
    (sourceLocalBall_isOpen K P _).measurableSet a
    (fun t => sourceJacquetBall_translate_mem_iff K P (R : ℤ) a t ha) _ (ψ₀ (-a)) hψ
  intro t ht
  have he (u : L) : f.val.val ((b.val * w₀ * n₀ x) * n₀ u) =
      ρ b (f.val.val (w₀ * n₀ (x + u))) := by
    rw [mul_assoc (b.val * w₀), sourceFiniteKP2ProjectiveLift_upper_add, mul_assoc b.val,
      f.val.property]
  unfold sourceKPJacquetCoordinateIntegrand
  rw [he, he, ← add_assoc x t a, hOuter t ht, neg_add, AddChar.map_add_eq_mul,
    mul_comm (ψ₀ (-t)), smul_smul]

theorem sourceKPJacquetCoordinateIntegral_open_inside
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C) (f : C) (b : B₀) (x : L) (R : ℕ)
    (hx : x ∈ B (R : ℤ)) :
    (∫ t in B (R : ℤ), E₀ f (b.val * w₀ * n₀ x) t ∂μ₀) = e (ρ b (ψ₀ x • Tr R f)) := by
  let A : (ι → ℂ) →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap
    (e.toLinearMap.comp ((ρ b).comp e.symm.toLinearMap))
  have hA (v : V) : A (e v) = e (ρ b v) := by
    change e (ρ b (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  have he : E₀ f (b.val * w₀ * n₀ x) = fun t => A (ψ₀ x • E₀ f w₀ (t + x)) := by
    funext t
    unfold sourceKPJacquetCoordinateIntegrand
    rw [mul_assoc (b.val * w₀), sourceFiniteKP2ProjectiveLift_upper_add, mul_assoc b.val,
      f.val.property, map_smul, map_smul, hA, smul_smul]
    have hp : ψ₀ x * ψ₀ (-(t + x)) = ψ₀ (-t) := by
      rw [← AddChar.map_add_eq_mul, show x + -(t + x) = -t by abel]
    rw [hp, add_comm t x]
  have hi := sourceKPJacquetCoordinateIntegrand_integrableOn K hζ P ρ C e hSmooth f w₀ R
  have hInv (t : L) : t + x ∈ B (R : ℤ) ↔ t ∈ B (R : ℤ) :=
    sourceJacquetBall_translate_mem_iff K P (R : ℤ) x t hx
  have hj : IntegrableOn (fun t => ψ₀ x • E₀ f w₀ (t + x)) (B (R : ℤ)) μ₀ := by
    change Integrable (ψ₀ x • (fun t : L => E₀ f w₀ (t + x))) ((μ₀).restrict (B (R : ℤ)))
    exact ((sourceKPJacquetSelfDual_translate_integrable_iff K P (B (R : ℤ)) x hInv (E₀ f w₀)).mpr hi).smul (ψ₀ x)
  rw [he, A.integral_comp_comm hj, integral_smul,
    sourceKPJacquetSelfDual_translate_integral K P (B (R : ℤ)) x hInv]
  calc
    _ = A (e (ψ₀ x • Tr R f)) := by
      unfold sourceKPJacquetTruncation
      simp only [map_smul, e.apply_symm_apply]
    _ = _ := hA _

variable (hC : ∀ (g : SourceFiniteKP2Projective K hζ P) (f : sourceAlgebraicInducedSpace _ ρ),
    f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P) ρ g f ∈ C)
    (hUpper : ∀ x : P.adicCompletion K, ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v)
    (hCube : ∀ y : (P.adicCompletion K)ˣ,
      sourceLocalValuation K P (((y ^ 3 : (P.adicCompletion K)ˣ) : P.adicCompletion K)) = 1 →
      ∀ v : V, ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y ^ 3)) v = v)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
local notation "J" => sourceKPJacquetStableMap K hζ P ρ C e hUpper hCube hSmooth
local notation "Av" => sourceKPJacquetUpperAverage K hζ P ρ C hC
local notation "r₀" => sourceKPJacquetRight K hζ P ρ C hC

theorem sourceKPJacquetUpperAverage_eventually_zero_of_kernel (f : C) (hf : J f = 0) :
    ∃ M R₀ : ℕ, ∀ R ≥ R₀, Av R M f = 0 := by
  obtain ⟨a, hψ⟩ := sourceKPJacquetSelfDual_fixed_shift_exists K P
  obtain ⟨M, hM⟩ := hSmooth f
  obtain ⟨T, ha, hOuter⟩ := sourceKPJacquet_open_cell_eventual_fixed_shift K hζ P ρ f.val hUpper hCube M
    (fun t ht => by simpa only [one_mul] using (hM t ht 1).2) a
  have hStable := sourceKPJacquetStableMap_hasStableValue K hζ P ρ C e hUpper hCube hSmooth f
  unfold SourceKPJacquetHasStableValue at hStable
  obtain ⟨N, hN⟩ := eventually_atTop.mp hStable
  refine ⟨M, max T N, fun R hR => ?_⟩
  have hTR : T ≤ R := (le_max_left _ _).trans hR
  have hNR : N ≤ R := (le_max_right _ _).trans hR
  have hSub : B (T : ℤ) ⊆ B (R : ℤ) := sourceKPJacquetSelfDual_ball_mono K P (by exact_mod_cast hTR)
  have haR := hSub ha
  have hTr : Tr R f = 0 := (hN R hNR).trans hf
  have hvol : (((μ₀).real (B (R : ℤ))) : ℂ) ≠ 0 := by
    exact_mod_cast (sourceLocalBall_volume_pos K P (R : ℤ)).ne'
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have hI : (∫ t in B (R : ℤ), E₀ f g t ∂μ₀) = 0 := by
    rcases sourceFiniteKP2Projective_bruhat_cells K hζ P g with ⟨b, rfl⟩ | ⟨b, x, rfl⟩
    · exact sourceKPJacquetCoordinateIntegral_closed K hζ P ρ C e hUpper f b R a haR hψ
    by_cases hx : x ∈ B (R : ℤ)
    · rw [sourceKPJacquetCoordinateIntegral_open_inside K hζ P ρ C e hSmooth f b x R hx,
        hTr, smul_zero, map_zero, map_zero]
    · apply sourceKPJacquetCoordinateIntegral_open_outside K hζ P ρ C e f b x R a haR hψ
      intro t ht
      exact hOuter (x + t) (fun h => hx ((sourceJacquetBall_translate_mem_iff K P (R : ℤ) t x ht).mp (hSub h)))
  have he := (sourceKPJacquetUpperAverage_eval_integral K hζ P ρ C hC e R M f g
    (fun u hu k => (hM u hu k).1)).trans hI
  have hz := (smul_eq_zero.mp he).resolve_left hvol
  exact e.injective (hz.trans (map_zero e).symm)

theorem sourceKPJacquet_kernel_le_whittaker_kernel (ℓ : C →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : L) (f : C), ℓ (r₀ (n₀ x) f) = ψ₀ x * ℓ f) :
    LinearMap.ker J ≤ LinearMap.ker ℓ := by
  intro f hf
  change J f = 0 at hf
  change ℓ f = 0
  obtain ⟨M, R, hR⟩ := sourceKPJacquetUpperAverage_eventually_zero_of_kernel K hζ P ρ C e hC hUpper hCube hSmooth f hf
  have h := sourceKPJacquetUpperAverage_whittaker K hζ P ρ C hC R M f ℓ hℓ
  rw [hR R le_rfl, map_zero] at h
  exact h.symm

private theorem linear_factor_through_range {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (j : X →ₗ[ℂ] Y) (ℓ : X →ₗ[ℂ] ℂ) (hker : LinearMap.ker j ≤ LinearMap.ker ℓ) :
    ∃ L₀ : LinearMap.range j →ₗ[ℂ] ℂ, ∀ f : X, L₀ (j.rangeRestrict f) = ℓ f := by
  refine ⟨((LinearMap.ker j).liftQ ℓ hker).comp j.quotKerEquivRange.symm.toLinearMap, ?_⟩
  intro f
  change (LinearMap.ker j).liftQ ℓ hker
    (j.quotKerEquivRange.symm ⟨j f, LinearMap.mem_range_self _ _⟩) = ℓ f
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem sourceKPJacquetLinearFactor_of_ker_le {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (j : X →ₗ[ℂ] Y) (ℓ : X →ₗ[ℂ] ℂ) (hker : LinearMap.ker j ≤ LinearMap.ker ℓ) :
    ∃ L₀ : Y →ₗ[ℂ] ℂ, ∀ f : X, L₀ (j f) = ℓ f := by
  obtain ⟨Lr, hLr⟩ := linear_factor_through_range j ℓ hker
  obtain ⟨L₀, hL₀⟩ := Lr.exists_extend
  refine ⟨L₀, fun f => ?_⟩
  exact (congrArg (fun u : LinearMap.range j →ₗ[ℂ] ℂ => u (j.rangeRestrict f)) hL₀).trans (hLr f)

end
end ArtinMatthews
