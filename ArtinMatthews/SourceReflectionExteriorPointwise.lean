module

public import ArtinMatthews.SourceReflectionExteriorFactors
public import ArtinMatthews.SourceReflectionSignedExteriorLocal


set_option backward.privateInPublic true
@[expose] public section

/-! Apply the local phases to the literal signed digit sums at every
prime on the original numerator and denominator support. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
  (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "U" => exteriorUnitSubgroup S
local notation "Γ" => SourceExteriorUnitSixthPowers S
local notation "a₀" => sourcePrimeExponentUnit K hζ S₀
local notation "f₀" => sourceReflectionActiveExponents K S₀
local notation "ν" => sourceReflectionExteriorFrequency K S₀ hζ
local notation "j" => sourceReflectionDigitIndex K S₀
local notation "D" => sourceReflectionDirectedCofactor K S₀ hζ
local notation "W" => fun P : Pr => sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS
local notation "R" => fun P : Pr => sourceReflectionTameRotatedActive K hζ S₀ P hS
local notation "Lext" => sourceReflectionSignedExteriorLocal K S₀ hζ hS

/-- The product of the prime contributions assigned to the three
separate factors, the two directed cross phases, and the base spherical value. -/
def sourceReflectionExteriorPlacedFactors (ε : U) (h : E) (f : Finset Pr)
    (a n d c : E) (P : Pr) : ℂ :=
  (if P ∈ h.support \ f then sourceReflectionExteriorInactiveFactor K S₀ P else 1) *
    (if P ∈ f then sourceReflectionExteriorFrozenPrime K S₀ hζ hS ε h f a n P else 1) *
    (if P ∈ d.support then sourceReflectionExteriorRowPrime K S₀ hζ hS ε f a n d P else 1) *
    (if P ∈ f then sourceReflectionExteriorRowActivePhase K S₀ hζ h a d P else 1) *
    (if P ∈ f then sourceReflectionExteriorColumnActivePhase K S₀ hζ h a c P else 1) *
    (if P ∈ c.support then sourceReflectionExteriorColumnPrime K S₀ hζ ε f a P else 1) *
    (if P ∈ d.support then (D P c : ℂ) else 1) *
    (if P ∈ c.support then (↑(D P d ^ (-4 : ℤ)) : ℂ) else 1) *
    W P (a₀ (c + 3 • n))

include hS in
private theorem active_local (ε : U) (γ : Γ) (h : E) (f : Finset Pr) (a n d c : E)
    (P : Pr) (hP : P ∈ f ∪ d.support) (e : ℕ)
    (hm : (a + c + 3 • n) P = e) (hb : (f₀ f + d) P = 1) :
    Lext P (h + d) (f ∪ d.support) (ν ε γ f a n d c) =
      R P (j (h + d) P) e
        (sourceReflectionFrequencyLocalUnit K S₀ hζ P
          (sourceReflectionExteriorSign K S₀ * (γ.val * ε))
          (a + c + 3 • n) (f₀ f + d)).val := by
  let C := P.val.adicCompletion K
  let j₀ := Units.map (RingHom.toMonoidHom (algebraMap K C))
  let π := sourceKPTameExteriorUniformizer K hζ S₀ P
  let v := sourceReflectionFrequencyLocalUnit K S₀ hζ P
    (sourceReflectionExteriorSign K S₀ * (γ.val * ε)) (a + c + 3 • n) (f₀ f + d)
  have hfac : j₀ (-(ν ε γ f a n d c)) = π ^ ((e : ℤ) - 2) * v.val := by
    have h' := sourceReflectionFrequencyLocalUnit_completion_signed K S₀ hζ P ε γ
      (a + c + 3 • n) (f₀ f + d)
    rw [hm, hb, Nat.cast_one, mul_one] at h'
    exact h'
  rw [sourceReflectionSignedExteriorLocal_active K S₀ hζ hS P _ _ _ hP, hfac]
  rfl

theorem sourceReflectionSignedExteriorLocal_factorized (ε : U) (γ : Γ) (h : E)
    (f : Finset Pr) (a n : E) (d c : ReflectionSquarefreeExponents K S₀)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) (ha : a.support ⊆ f)
    (hdh : Disjoint d.val.support h.support) (hdn : Disjoint d.val.support n.support)
    (hdc : Disjoint d.val.support c.val.support) (hfc : Disjoint f c.val.support)
    (hfn : Disjoint f n.support) (P : Pr) :
    Lext P (h + d.val) (f ∪ d.val.support) (ν ε γ f a n d.val c.val) =
      sourceReflectionExteriorPlacedFactors K S₀ hζ hS ε h f a n d.val c.val P := by
  have hfsub := sourceReflectionActiveChoice_subset K S₀ hf
  by_cases hPf : P ∈ f
  · have hPd : P ∉ d.val.support := fun hm => Finset.disjoint_left.mp hdh hm (hfsub hPf)
    have hPc : P ∉ c.val.support := Finset.disjoint_left.mp hfc hPf
    have hPn : P ∉ n.support := Finset.disjoint_left.mp hfn hPf
    have hm : (a + c.val + 3 • n) P = a P := by
      simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hPc,
        Finsupp.notMem_support_iff.mp hPn]
    have hb : (f₀ f + d.val) P = 1 := by
      rw [Finsupp.add_apply, sourceReflectionActiveExponents_apply K S₀,
        ite_eq_left hPf, Finsupp.notMem_support_iff.mp hPd, add_zero]
    have hw : W P (a₀ (c.val + 3 • n)) = 1 := by
      apply sourceKPTameExteriorWhittakerDiagonal_exponent_zero
      simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hPc,
        Finsupp.notMem_support_iff.mp hPn]
    have hPi : P ∉ h.support \ f := fun hp => (Finset.mem_sdiff.mp hp).2 hPf
    rw [active_local K S₀ hζ hS ε γ h f a n d.val c.val P (Finset.mem_union_left _ hPf) (a P) hm hb,
      sourceReflectionDigitIndex_off_row K S₀ h d.val hPd]
    refine (sourceReflectionActiveFrequency_factor K S₀ hζ P hS ε γ f a n d.val c.val (j h P) (a P)).trans ?_
    simp only [sourceReflectionExteriorPlacedFactors, ite_eq_right hPi, ite_eq_left hPf, ite_eq_right hPd, ite_eq_right hPc,
      sourceReflectionExteriorFrozenPrime, sourceReflectionExteriorRowActivePhase,
      sourceReflectionExteriorColumnActivePhase, hw, one_mul, mul_one]
  · have ha0 : a P = 0 := Finsupp.notMem_support_iff.mp (fun hm => hPf (ha hm))
    by_cases hPd : P ∈ d.val.support
    · have hPh : P ∉ h.support := Finset.disjoint_left.mp hdh hPd
      have hPn : P ∉ n.support := Finset.disjoint_left.mp hdn hPd
      have hPc : P ∉ c.val.support := Finset.disjoint_left.mp hdc hPd
      have hm : (a + c.val + 3 • n) P = 0 := by
        simp [Finsupp.add_apply, Finsupp.smul_apply, ha0, Finsupp.notMem_support_iff.mp hPc,
          Finsupp.notMem_support_iff.mp hPn]
      have hb : (f₀ f + d.val) P = 1 := by
        rw [Finsupp.add_apply, sourceReflectionActiveExponents_apply K S₀, ite_eq_right hPf, zero_add]
        exact reflectionSquarefreeExponent_support_one K S₀ d ⟨P,hPd⟩
      have hw : W P (a₀ (c.val + 3 • n)) = 1 := by
        apply sourceKPTameExteriorWhittakerDiagonal_exponent_zero
        simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hPc,
          Finsupp.notMem_support_iff.mp hPn]
      have hPi : P ∉ h.support \ f := fun hp => hPh (Finset.mem_sdiff.mp hp).1
      rw [active_local K S₀ hζ hS ε γ h f a n d.val c.val P (Finset.mem_union_right _ hPd) 0 hm hb,
        sourceReflectionDigitIndex_row K S₀ d.property hdh hPd]
      refine (sourceReflectionActiveFrequency_row_factor K S₀ hζ P hS ε γ f a n d.val c.val).trans ?_
      simp only [sourceReflectionExteriorPlacedFactors, ite_eq_right hPi, ite_eq_right hPf, ite_eq_left hPd, ite_eq_right hPc,
        sourceReflectionExteriorRowPrime, hw, one_mul, mul_one]
    · have hp : P ∉ f ∪ d.val.support := by simpa [hPf, hPd]
      have hb : (f₀ f + d.val) P = 0 := by
        rw [Finsupp.add_apply, sourceReflectionActiveExponents_apply K S₀,
          ite_eq_right hPf, Finsupp.notMem_support_iff.mp hPd, add_zero]
      have hi : (if P ∈ (h + d.val).support then
          sourceReflectionTameFourierCoefficient K hζ S₀ P (j (h + d.val) P) 0 else 1) =
          (if P ∈ h.support \ f then sourceReflectionExteriorInactiveFactor K S₀ P else 1) := by
        have hmem : P ∈ (h + d.val).support ↔ P ∈ h.support :=
          (sourceReflectionExteriorRow_mem K S₀ h d.val P).trans (by simp [hPd])
        by_cases hh : P ∈ h.support
        · have hhi := Finset.mem_sdiff.mpr ⟨hh,hPf⟩
          rw [ite_eq_left (hmem.mpr hh), ite_eq_left hhi, sourceReflectionDigitIndex_off_row K S₀ h d.val hPd,
            sourceReflectionActiveChoice_digit_zero K S₀ hf hh hPf,
            sourceReflectionTameFourierCoefficient_zero, ite_eq_left rfl]
          rfl
        · have hhi : P ∉ h.support \ f := fun hm => hh (Finset.mem_sdiff.mp hm).1
          rw [ite_eq_right (fun h => hh (hmem.mp h)), ite_eq_right hhi]
      rw [sourceReflectionSignedExteriorLocal_inactive K S₀ hζ hS P _ _ _ hp]
      change (if P ∈ (h + d.val).support then
        sourceReflectionTameFourierCoefficient K hζ S₀ P (j (h + d.val) P) 0 else 1) * _ = _
      rw [hi, sourceReflectionSphericalFrequency_factor K S₀ hζ P hS ε γ f a n d.val c ha0 hb,
        sourceReflectionExteriorPlacedFactors]
      by_cases hPc : P ∈ c.val.support
      · simp only [ite_eq_right hPf, ite_eq_right hPd, ite_eq_left hPc, Units.val_mul,
          sourceReflectionExteriorColumnPrime, mul_one, mul_assoc]
      · simp only [ite_eq_right hPf, ite_eq_right hPd, ite_eq_right hPc, mul_one, one_mul]

end
end ArtinMatthews.SourceEulerAssembly
