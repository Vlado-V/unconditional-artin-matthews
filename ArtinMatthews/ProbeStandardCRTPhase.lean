module

public import ArtinMatthews.ProbeStandardTraceModulus
public import ArtinMatthews.ProbeIdealCRTTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Standard global trace phases under an actual prime-power factorization.
The comparison units with the coherent local tower are derived, not assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def probeStandardCRTPhase (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a}))
    (hN : probeIdealCRTModulus K P n = Ideal.span {a}) :
    AddChar ((𝓞 K) ⧸ probeIdealCRTModulus K P n) ℂ :=
  (probeStandardTraceModChar K a ha hcop).compAddMonoidHom
    (Ideal.quotEquivOfEq hN).toAddMonoidHom

omit [DecidableEq ι] in
theorem probeStandardCRTPhase_mk (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a}))
    (hN : probeIdealCRTModulus K P n = Ideal.span {a}) (x : 𝓞 K) :
    probeStandardCRTPhase K P n a ha hcop hN (Ideal.Quotient.mk _ x) =
      Complex.exp ((Algebra.trace ℚ K ((x : K) / (a : K)) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) := by
  change probeStandardTraceModChar K a ha hcop
    (Ideal.quotEquivOfEq hN (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.quotEquivOfEq_mk, probeStandardTraceModChar_mk]

omit [DecidableEq ι] in
theorem probeStandardCRTPhase_primitive (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a}))
    (hN : probeIdealCRTModulus K P n = Ideal.span {a}) :
    (probeStandardCRTPhase K P n a ha hcop hN).IsPrimitive :=
  probeAddChar_transport_primitive (Ideal.quotEquivOfEq hN)
    (probeStandardTraceModChar K a ha hcop) (probeStandardTraceModChar_primitive K a ha hcop)

theorem probeStandardCRTPhase_component_unit
    (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a}))
    (hN : probeIdealCRTModulus K P n = Ideal.span {a}) (i : ι) :
    ∃ u : ((𝓞 K) ⧸ (P i).asIdeal ^ n i)ˣ,
      (probeIdealPhase K (P i) (n i)).mulShift (u : _) =
        probeCRTAddCharComponent (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ n j)
          (probeIdealCRTEquiv K P n hP) (probeStandardCRTPhase K P n a ha hcop hN) i := by
  let : Finite ((𝓞 K) ⧸ (P i).asIdeal ^ n i) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (P i).ne_bot)
  let : Fintype ((𝓞 K) ⧸ (P i).asIdeal ^ n i) := Fintype.ofFinite _
  apply probe_addChar_exists_unit_shift _ _ (probeIdealPhase_primitive K (P i) (n i))
  exact probeCRTAddCharComponent_primitive _ _ _
    (probeStandardCRTPhase_primitive K P n a ha hcop hN) i

theorem probeStandardCRTPhase_factor (P : ι → HeightOneSpectrum (𝓞 K)) (n : ι → ℕ)
    (hP : Pairwise fun i j => P i ≠ P j)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hcop : IsCoprime (differentIdeal ℤ (𝓞 K)) (Ideal.span {a}))
    (hN : probeIdealCRTModulus K P n = Ideal.span {a}) (x : 𝓞 K) :
    Complex.exp ((Algebra.trace ℚ K ((x : K) / (a : K)) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) =
      ∏ i, probeCRTAddCharComponent (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ n j)
        (probeIdealCRTEquiv K P n hP) (probeStandardCRTPhase K P n a ha hcop hN) i
          (Ideal.Quotient.mk ((P i).asIdeal ^ n i) x) := by
  rw [← probeStandardCRTPhase_mk K P n a ha hcop hN x,
    probeCRTAddChar_factor (fun j => (𝓞 K) ⧸ (P j).asIdeal ^ n j)
      (probeIdealCRTEquiv K P n hP)]
  simp only [probeIdealCRTEquiv_mk]

end
end ArtinMatthews.VaryingKummerAnalytic
