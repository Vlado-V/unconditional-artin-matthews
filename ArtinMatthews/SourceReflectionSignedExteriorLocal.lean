module

public import ArtinMatthews.SourceReflectionTameRotationSupport
public import ArtinMatthews.SourceReflectionFieldFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! The literal signed Weyl factors on the exterior places. The inactive
row coefficient is kept only at primes belonging to the original row. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀

section Place

variable (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "D₀" => fun a : Lˣ => l₀ (sourceGL2Diagonal a)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "N₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
local notation "Wext" => sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS
local notation "C₀" => sourceReflectionTameFourierCoefficient K hζ S₀ P
local notation "u₀" => sourceReflectionTameUnitLift K S₀ P
local notation "j₀" => Units.map (RingHom.toMonoidHom (algebraMap K L))

local instance sourceReflectionSignedExteriorLocalResidueField : Field R :=
  let : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _
local instance sourceReflectionSignedExteriorLocalResidueFinite : Finite R :=
  Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance sourceReflectionSignedExteriorLocalResidueFintype : Fintype R := Fintype.ofFinite _

def sourceReflectionSignedExteriorWeylValue (a : Kˣ) (x : L) : ℂ :=
  W₀ (D₀ (j₀ a) * (D₀ (sourceMinusOneUnit L) * w₀) * N₀ x)

local notation "V" => sourceReflectionSignedExteriorWeylValue K S₀ hζ hS P

theorem sourceReflectionSignedExteriorWeylValue_eq_negative (a : Kˣ) (x : L) :
    V a x = W₀ (D₀ (j₀ (-a)) * w₀ * N₀ x) := by
  have he : j₀ a * sourceMinusOneUnit L = j₀ (-a) := by
    apply Units.ext
    change algebraMap K L (a : K) * (-1 : L) = algebraMap K L (-(a : K))
    rw [mul_neg_one, map_neg]
  unfold sourceReflectionSignedExteriorWeylValue
  rw [← mul_assoc (D₀ (j₀ a)), sourceFiniteKP2ProjectiveLift_diagonal_mul,
    sourceFiniteKPHilbert_minus_right, one_pow, map_one, one_mul, he]

theorem sourceReflectionSignedExteriorWeylValue_zero_shift (a : Kˣ) : V a 0 = Wext a := by
  have hN : N₀ (0 : L) = 1 := by
    change l₀ (sourceGL2Upper (0 : L)) = 1
    rw [sourceGL2Upper_zero]
    exact (sourceFiniteKP2ProjectiveMk K hζ P.val).map_one
  rw [sourceReflectionSignedExteriorWeylValue_eq_negative, hN, mul_one,
    sourceKPTameCyclicWhittakerValue_weyl_right K hζ S₀ P hS]
  exact sourceKPTameExteriorWhittakerDiagonal_neg K hζ S₀ hS P a

def sourceReflectionSignedExteriorLocal (row : E) (active : Finset Pr) (a : Kˣ) : ℂ :=
  let j : Fin 6 := ⟨row P % 6, Nat.mod_lt _ (by decide)⟩
  if P ∈ active then
    ∑ h : Rˣ, C₀ j h * V a ((π₀ ^ (-1 : ℤ) * u₀ h : Lˣ) : L)
  else if P ∈ row.support then C₀ j 0 * V a 0 else V a 0

local notation "F" => sourceReflectionSignedExteriorLocal K S₀ hζ hS P

theorem sourceReflectionSignedExteriorLocal_active (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∈ active) :
    F row active a = ∑ h : Rˣ, C₀ ⟨row P % 6, Nat.mod_lt _ (by decide)⟩ h *
      W₀ (D₀ (j₀ (-a)) * w₀ * N₀ ((π₀ ^ (-1 : ℤ) * u₀ h : Lˣ) : L)) := by
  unfold sourceReflectionSignedExteriorLocal
  rw [ite_eq_left hP]
  apply Finset.sum_congr rfl
  intro h _
  rw [sourceReflectionSignedExteriorWeylValue_eq_negative]

theorem sourceReflectionSignedExteriorLocal_inactive (row : E) (active : Finset Pr)
    (a : Kˣ) (hP : P ∉ active) :
    F row active a = (if P ∈ row.support then C₀ ⟨row P % 6, Nat.mod_lt _ (by decide)⟩ 0 else 1) * Wext a := by
  unfold sourceReflectionSignedExteriorLocal
  rw [ite_eq_right hP, sourceReflectionSignedExteriorWeylValue_zero_shift]
  split_ifs <;> simp only [one_mul]

theorem sourceReflectionExterior_completion_order (a : Kˣ) :
    sourceKPValuationOrder ν₀ (j₀ a) = exteriorPrincipalValuation P.val a := by
  rw [sourceExteriorPrincipalValuation_eq_neg_log]
  have h := sourceKPValuationOrder_spec ν₀ (j₀ a)
  change Valued.v (algebraMap K L (a : K)) = _ at h
  have hv : Valued.v (algebraMap K L (a : K)) = P.val.valuation K (a : K) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P.val (a : K)
  rw [hv] at h
  rw [h, WithZero.log_exp, neg_neg]

theorem sourceReflectionExterior_completion_order_neg (a : Kˣ) :
    sourceKPValuationOrder ν₀ (j₀ (-a)) = exteriorPrincipalValuation P.val a := by
  rw [sourceReflectionExterior_completion_order, sourceExteriorPrincipalValuation_eq_neg_log,
    sourceExteriorPrincipalValuation_eq_neg_log, Units.val_neg, Valuation.map_neg]

theorem sourceReflectionTameExteriorWhittaker_eq_one_of_order_zero (a : Kˣ)
    (ha : exteriorPrincipalValuation P.val a = 0) : Wext a = 1 := by
  have hν := (sourceKPValuationOrder_eq ν₀ (j₀ a) 0).mp
    ((sourceReflectionExterior_completion_order K S₀ P a).trans ha)
  have hu : ν₀ ((j₀ a : Lˣ) : L) = 1 := by simpa only [neg_zero, WithZero.exp_zero] using hν
  have hd := sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS 0 (j₀ a) hu
  simp only [zpow_zero, one_mul, mul_zero] at hd
  change W₀ (D₀ (j₀ a)) = 1
  rw [hd, show sourceGL2Diagonal (1 : Lˣ) = 1 from (sourceGL2DiagonalHom L).map_one,
    show l₀ 1 = 1 from (sourceFiniteKP2ProjectiveMk K hζ P.val).map_one,
    sourceKPTameCyclicWhittakerValue_one K hζ S₀ P hS]

theorem sourceReflectionTameExteriorWhittaker_zero_of_negative_order (a : Kˣ)
    (ha : exteriorPrincipalValuation P.val a < 0) : Wext a = 0 := by
  apply sourceKPTameCyclicWhittakerValue_diagonal_order_negative K hζ S₀ P hS
  rwa [sourceReflectionExterior_completion_order K S₀ P]

theorem sourceReflectionTameExteriorWhittaker_zero_of_mod_three (a : Kˣ)
    (ha : 0 ≤ exteriorPrincipalValuation P.val a)
    (hm : exteriorPrincipalValuation P.val a % 3 = 2) : Wext a = 0 := by
  let e := exteriorPrincipalValuation P.val a
  let k := e.toNat / 3
  let v := sourceKPUnitPart ν₀ π₀ (j₀ a)
  have hv : ν₀ (v : L) = 1 := sourceKPUnitPart_valuation ν₀ π₀ hπ₀ _
  have he : e = ((3 * k + 2 : ℕ) : ℤ) := by
    dsimp only [e, k]
    omega
  have hfac : j₀ a = π₀ ^ ((3 * k + 2 : ℕ) : ℤ) * v := by
    have ho : sourceKPValuationOrder ν₀ (j₀ a) = e :=
      sourceReflectionExterior_completion_order K S₀ P a
    rw [← he, ← ho]
    exact (sourceKPUnitPart_factor ν₀ π₀ (j₀ a)).symm
  change W₀ (D₀ (j₀ a)) = 0
  rw [hfac, sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS _ _ hv,
    sourceKPTameCyclicWhittakerValue_diagonal_three_add_two K hζ S₀ P hS, mul_zero]

end Place
end
end ArtinMatthews.SourceEulerAssembly
