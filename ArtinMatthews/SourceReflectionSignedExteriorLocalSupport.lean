module

public import ArtinMatthews.SourceReflectionSignedExteriorLocal
public import ArtinMatthews.SourceReflectionTameRotationWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The signed local Fourier branches enforce the exact lower order,
modulo-three, and distinguished-row support restrictions. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (P : SourceExteriorPrime K S₀)

local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "j₀" => Units.map (RingHom.toMonoidHom (algebraMap K L))
local notation "ord" => exteriorPrincipalValuation P.val
local notation "F" => sourceReflectionSignedExteriorLocal K S₀ hζ hS P
local notation "Rot" => sourceReflectionTameRotatedActive K hζ S₀ P hS

theorem sourceReflectionSignedExteriorLocal_active_decompose (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∈ active) (e : ℕ) (he : ord a = (e : ℤ) - 2) :
    ∃ v : Lˣ, ν₀ (v : L) = 1 ∧ j₀ (-a) = π₀ ^ ((e : ℤ) - 2) * v ∧
      F row active a = Rot ⟨row P % 6, Nat.mod_lt _ (by decide)⟩ e v := by
  let v := sourceKPUnitPart ν₀ π₀ (j₀ (-a))
  have hv : ν₀ (v : L) = 1 := sourceKPUnitPart_valuation ν₀ π₀ hπ₀ _
  have hfac : j₀ (-a) = π₀ ^ ((e : ℤ) - 2) * v := by
    rw [← he, ← sourceReflectionExterior_completion_order_neg K S₀ P a]
    exact (sourceKPUnitPart_factor ν₀ π₀ (j₀ (-a))).symm
  refine ⟨v, hv, hfac, ?_⟩
  rw [sourceReflectionSignedExteriorLocal_active K S₀ hζ hS P row active a hP, hfac]
  rfl

theorem sourceReflectionSignedExteriorLocal_active_zero_of_negative_order (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∈ active) (ha : ord a < -2) : F row active a = 0 := by
  have hπ := (sourceKPValuationOrder_eq ν₀ π₀ 1).mpr hπ₀
  have ho : sourceKPValuationOrder ν₀ (j₀ (-a) * (π₀ * 1) ^ (2 : ℤ)) < 0 := by
    rw [mul_one, sourceKPValuationOrder_mul, sourceKPValuationOrder_zpow, hπ,
      mul_one, sourceReflectionExterior_completion_order_neg K S₀ P a]
    omega
  rw [sourceReflectionSignedExteriorLocal_active K S₀ hζ hS P row active a hP]
  exact sourceReflectionTameRotatedActive_zero_of_negative_order K hζ S₀ P hS
    ⟨row P % 6, Nat.mod_lt _ (by decide)⟩ (j₀ (-a)) 1 (by simp) ho

theorem sourceReflectionSignedExteriorLocal_inactive_zero_of_negative_order (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∉ active) (ha : ord a < 0) : F row active a = 0 := by
  rw [sourceReflectionSignedExteriorLocal_inactive K S₀ hζ hS P row active a hP,
    sourceReflectionTameExteriorWhittaker_zero_of_negative_order K S₀ hζ hS P a ha, mul_zero]

theorem sourceReflectionSignedExteriorLocal_active_zero_of_mod_three (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∈ active) (ha : -2 ≤ ord a)
    (hm : (ord a + 2) % 3 = 2) : F row active a = 0 := by
  let e := (ord a + 2).toNat
  have he : ord a = (e : ℤ) - 2 := by dsimp only [e]; omega
  have hm' : e % 3 = 2 := by dsimp only [e]; omega
  have he0 : e ≠ 0 := by omega
  obtain ⟨v, hv, _, hfac⟩ := sourceReflectionSignedExteriorLocal_active_decompose K S₀ hζ hS P row active a hP e he
  apply norm_eq_zero.mp
  rw [hfac, sourceReflectionTameRotatedActive_norm_eq K hζ S₀ P hS _ e v hv]
  have hw : sourceReflectionFrozenLocalWeight (Ideal.absNorm P.val.asIdeal : ℝ) e = 0 := by
    simp [sourceReflectionFrozenLocalWeight, he0, hm']
  simp [he0, hw]

theorem sourceReflectionSignedExteriorLocal_inactive_zero_of_mod_three (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∉ active) (ha : 0 ≤ ord a) (hm : ord a % 3 = 2) : F row active a = 0 := by
  rw [sourceReflectionSignedExteriorLocal_inactive K S₀ hζ hS P row active a hP,
    sourceReflectionTameExteriorWhittaker_zero_of_mod_three K S₀ hζ hS P a ha hm, mul_zero]

theorem sourceReflectionSignedExteriorLocal_active_zero_of_positive_cleared_order (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∈ active) (hj : row P % 6 ≠ 4)
    (ha : -2 < ord a) : F row active a = 0 := by
  let e := (ord a + 2).toNat
  let j : Fin 6 := ⟨row P % 6, Nat.mod_lt _ (by decide)⟩
  have he : ord a = (e : ℤ) - 2 := by dsimp only [e]; omega
  have he0 : e ≠ 0 := by omega
  have hj' : j ≠ 4 := fun h => hj (congrArg Fin.val h)
  obtain ⟨v, hv, _, hfac⟩ := sourceReflectionSignedExteriorLocal_active_decompose K S₀ hζ hS P row active a hP e he
  change F row active a = Rot j e v at hfac
  apply norm_eq_zero.mp
  rw [hfac, sourceReflectionTameRotatedActive_norm_eq K hζ S₀ P hS j e v hv]
  simp only [ite_eq_right he0, ite_eq_right hj']

end
end ArtinMatthews.SourceEulerAssembly
