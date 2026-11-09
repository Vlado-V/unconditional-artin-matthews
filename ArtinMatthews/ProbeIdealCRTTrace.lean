module

public import ArtinMatthews.ProbeCRTAdditiveComponents
public import ArtinMatthews.ProbeIdealPrimeFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The actual global ideal-trace character factors through CRT. Its local
components are proved unit shifts of the constructed coherent local phases. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def probeIdealCRTModulus (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ) : Ideal (𝓞 K) :=
  ∏ i, (P i).asIdeal ^ n i

omit [NumberField K] [DecidableEq ι] in
theorem probeIdealCRTModulus_ne_zero (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ) :
    probeIdealCRTModulus K P n ≠ ⊥ := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (P i).ne_bot

def probeIdealCRTEquiv (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) :
    ((𝓞 K) ⧸ probeIdealCRTModulus K P n) ≃+* ∀ i, (𝓞 K) ⧸ (P i).asIdeal ^ n i :=
  HeightOneSpectrum.quotientEquivPiOfProdEq _ P n hP rfl

omit [DecidableEq ι] in
theorem probeIdealCRTEquiv_mk (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (x : 𝓞 K) (i : ι) :
    probeIdealCRTEquiv K P n hP (Ideal.Quotient.mk _ x) i =
      Ideal.Quotient.mk ((P i).asIdeal ^ n i) x := by
  simp only [probeIdealCRTEquiv, HeightOneSpectrum.quotientEquivPiOfProdEq,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

def probeIdealCRTGlobalPhase (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ) :
    AddChar ((𝓞 K) ⧸ probeIdealCRTModulus K P n) ℂ :=
  (idealTraceAddChar K _ (probeIdealCRTModulus_ne_zero K P n))⁻¹

omit [DecidableEq ι] in
theorem probeIdealCRTGlobalPhase_primitive (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ) :
    (probeIdealCRTGlobalPhase K P n).IsPrimitive := by
  intro x hx
  rw [probeIdealCRTGlobalPhase, AddChar.inv_mulShift, AddChar.mulShift_mulShift, neg_one_mul]
  exact idealTraceAddChar_isPrimitive K _ (probeIdealCRTModulus_ne_zero K P n)
    (neg_ne_zero.mpr hx)

def probeIdealCRTLocalPhase (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (i : ι) : AddChar ((𝓞 K) ⧸ (P i).asIdeal ^ n i) ℂ :=
  probeCRTAddCharComponent (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ n j)
    (probeIdealCRTEquiv K P n hP) (probeIdealCRTGlobalPhase K P n) i

theorem probeIdealCRTLocalPhase_primitive (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (i : ι) :
    (probeIdealCRTLocalPhase K P n hP i).IsPrimitive :=
  probeCRTAddCharComponent_primitive _ _ _ (probeIdealCRTGlobalPhase_primitive K P n) i

theorem probeIdealCRTGlobalPhase_factor (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (x : 𝓞 K) :
    probeIdealCRTGlobalPhase K P n (Ideal.Quotient.mk _ x) =
      ∏ i, probeIdealCRTLocalPhase K P n hP i (Ideal.Quotient.mk _ x) := by
  rw [probeCRTAddChar_factor (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ n j)
    (probeIdealCRTEquiv K P n hP)]
  simp only [probeIdealCRTEquiv_mk, probeIdealCRTLocalPhase]

theorem probeIdealCRTLocalPhase_exists_unit (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (i : ι) :
    ∃ u : ((𝓞 K) ⧸ (P i).asIdeal ^ n i)ˣ,
      (probeIdealPhase K (P i) (n i)).mulShift (u : _) = probeIdealCRTLocalPhase K P n hP i := by
  let : Finite ((𝓞 K) ⧸ (P i).asIdeal ^ n i) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (P i).ne_bot)
  let : Fintype ((𝓞 K) ⧸ (P i).asIdeal ^ n i) := Fintype.ofFinite _
  exact probe_addChar_exists_unit_shift _ _ (probeIdealPhase_primitive K (P i) (n i))
    (probeIdealCRTLocalPhase_primitive K P n hP i)

def probeIdealCRTComparisonUnit (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (i : ι) : ((𝓞 K) ⧸ (P i).asIdeal ^ n i)ˣ :=
  (probeIdealCRTLocalPhase_exists_unit K P n hP i).choose

theorem probeIdealCRTComparisonUnit_spec (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (i : ι) :
    (probeIdealPhase K (P i) (n i)).mulShift
      (probeIdealCRTComparisonUnit K P n hP i : _) = probeIdealCRTLocalPhase K P n hP i :=
  (probeIdealCRTLocalPhase_exists_unit K P n hP i).choose_spec

theorem probeIdealCRTGlobalPhase_factor_coherent (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j) (x : 𝓞 K) :
    probeIdealCRTGlobalPhase K P n (Ideal.Quotient.mk _ x) =
      ∏ i, probeIdealPhase K (P i) (n i)
        ((probeIdealCRTComparisonUnit K P n hP i : (𝓞 K) ⧸ (P i).asIdeal ^ n i) *
          Ideal.Quotient.mk ((P i).asIdeal ^ n i) x) := by
  rw [probeIdealCRTGlobalPhase_factor K P n hP x]
  apply Finset.prod_congr rfl
  intro i _
  have he := congrArg (fun ψ : AddChar ((𝓞 K) ⧸ (P i).asIdeal ^ n i) ℂ =>
    ψ (Ideal.Quotient.mk _ x)) (probeIdealCRTComparisonUnit_spec K P n hP i)
  exact he.symm

end
end ArtinMatthews.VaryingKummerAnalytic
