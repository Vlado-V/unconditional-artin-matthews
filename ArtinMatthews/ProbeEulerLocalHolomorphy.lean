module

public import ArtinMatthews.ProbeEulerPrimeNorms
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphy and an absolutely summable principal logarithm for the
literal source-05 rational correction. No local Gauss identification is
used here. -/

namespace ArtinMatthews

noncomputable section
open NumberField IsDedekindDomain Set Filter
open scoped NumberField Classical BigOperators Topology

abbrev ProbeCoordinates := ℂ × ℂ × ℂ

def probeEulerDomain : Set ProbeCoordinates :=
  {p | probeEulerRegion p.1.re p.2.1.re p.2.2.re}

variable (K : Type*) [Field K] [NumberField K]

def probePrimeCorrection (a b c : ProbePrime K → ℂ) (P : ProbePrime K)
    (p : ProbeCoordinates) : ℂ :=
  probeGoodPrimeCorrection (Ideal.absNorm P.asIdeal) (a P) (b P) (c P)
    p.1 p.2.1 p.2.2

def probePrimeLog (a b c : ProbePrime K → ℂ) (P : ProbePrime K)
    (p : ProbeCoordinates) : ℂ := Complex.log (probePrimeCorrection K a b c P p)

theorem probePrimeCorrection_norm_sub_one_le (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (S : Finset (ProbePrime K)) (hS : probePrimeCutoff K ⊆ S)
    (P : ProbeGoodPrime K S) {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    ‖probePrimeCorrection K a b c P.val p - 1‖ ≤ 160 * probePrimeWeight K P.val := by
  obtain ⟨hQ, hsmall, _⟩ := probeGoodPrime_norm_bounds K S hS P
  exact probeGoodPrimeCorrection_norm_sub_one_le _ hQ hsmall _ _ _ _ _ _
    (ha P.val) (hb P.val) (hc P.val) hp

theorem probePrimeCorrection_norm_sub_one_half (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (S : Finset (ProbePrime K)) (hS : probePrimeCutoff K ⊆ S)
    (P : ProbeGoodPrime K S) {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    ‖probePrimeCorrection K a b c P.val p - 1‖ ≤ 1 / 2 :=
  (probePrimeCorrection_norm_sub_one_le K a b c ha hb hc S hS P hp).trans
    (probeGoodPrime_norm_bounds K S hS P).2.2

theorem probePrimeCorrection_mem_slitPlane (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (S : Finset (ProbePrime K)) (hS : probePrimeCutoff K ⊆ S)
    (P : ProbeGoodPrime K S) {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    probePrimeCorrection K a b c P.val p ∈ Complex.slitPlane := by
  have hh := probePrimeCorrection_norm_sub_one_half K a b c ha hb hc S hS P hp
  simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one
    (z := probePrimeCorrection K a b c P.val p - 1) (lt_of_le_of_lt hh (by norm_num))

theorem probePrimeCorrection_ne_zero (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (S : Finset (ProbePrime K)) (hS : probePrimeCutoff K ⊆ S)
    (P : ProbeGoodPrime K S) {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    probePrimeCorrection K a b c P.val p ≠ 0 :=
  Complex.slitPlane_ne_zero (probePrimeCorrection_mem_slitPlane K a b c ha hb hc S hS P hp)

theorem probePrimeLog_norm_le (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (S : Finset (ProbePrime K)) (hS : probePrimeCutoff K ⊆ S)
    (P : ProbeGoodPrime K S) {p : ProbeCoordinates} (hp : p ∈ probeEulerDomain) :
    ‖probePrimeLog K a b c P.val p‖ ≤ 240 * probePrimeWeight K P.val := by
  have hh := probePrimeCorrection_norm_sub_one_half K a b c ha hb hc S hS P hp
  have hl := Complex.norm_log_one_add_half_le_self
    (z := probePrimeCorrection K a b c P.val p - 1) hh
  simp only [add_sub_cancel] at hl
  calc
    _ ≤ (3 / 2) * ‖probePrimeCorrection K a b c P.val p - 1‖ := hl
    _ ≤ (3 / 2) * (160 * probePrimeWeight K P.val) :=
      mul_le_mul_of_nonneg_left
        (probePrimeCorrection_norm_sub_one_le K a b c ha hb hc S hS P hp) (by norm_num)
    _ = _ := by ring

theorem probeGoodPrimeCorrection_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Q : ℝ} (hQ : 1 ≤ Q) (hsmall : Q ^ (-(299 / 100000 : ℝ)) ≤ 1 / 2)
    {a b c : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    {x w z : E → ℂ} {t : E} (hx : DifferentiableAt ℂ x t)
    (hw : DifferentiableAt ℂ w t) (hz : DifferentiableAt ℂ z t)
    (ht : probeEulerRegion (x t).re (w t).re (z t).re) :
    DifferentiableAt ℂ (fun u => probeGoodPrimeCorrection Q a b c (x u) (w u) (z u)) t := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hV : DifferentiableAt ℂ (fun u => probeLocalV Q (z u)) t :=
    (hz.const_mul 6).neg.const_cpow (Or.inl hQne)
  have hW : DifferentiableAt ℂ (fun u => probeLocalW Q a (w u)) t :=
    (hw.neg.const_cpow (Or.inl hQne)).const_mul a
  have hD : DifferentiableAt ℂ (fun u => probeLocalD Q b (x u)) t :=
    (hx.neg.const_cpow (Or.inl hQne)).const_mul b
  have hE : DifferentiableAt ℂ (fun u => probeLocalE Q c (x u) (z u)) t :=
    (((differentiableAt_const (4 : ℂ)).sub (hx.const_mul 6)).sub
      (hz.const_mul 6)).const_cpow (Or.inl hQne) |>.const_mul c
  obtain ⟨hxr, hwr, hvr, her⟩ := probeEulerRegion_individual ht
  have hhalf {v r : ℝ} (hv : v ≤ Q ^ (-r)) (hr : 299 / 100000 ≤ r) : v ≤ 1 / 2 :=
    (hv.trans (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))).trans hsmall
  have hv0 := probe_one_sub_ne_zero (hhalf (probeLocalV_norm Q hQ0 (z t)).le hvr)
  have hw0 := probe_one_sub_ne_zero (hhalf (probeLocalW_norm_le Q hQ0 a (w t) ha) hwr)
  have hd0 := probe_one_sub_ne_zero (hhalf (probeLocalD_norm_le Q hQ0 b (x t) hb) hxr)
  have he0 := probe_one_sub_ne_zero (hhalf (probeLocalE_norm_le Q hQ0 c (x t) (z t) hc) her)
  have hone : DifferentiableAt ℂ (fun _ : E => (1 : ℂ)) t := differentiableAt_const 1
  have hq : DifferentiableAt ℂ (fun _ : E => (Q : ℂ) - 1) t := differentiableAt_const _
  have hq' : DifferentiableAt ℂ (fun _ : E => 1 - (Q : ℂ)⁻¹) t := differentiableAt_const _
  have hVi := (hone.sub hV).inv hv0
  have hWi := (hone.sub hW).inv hw0
  have hDi := (hone.sub hD).inv hd0
  have hEi := (hone.sub hE).inv he0
  simpa only [probeGoodPrimeCorrection, probeGoodLocalCorrection, probeGoodLocalFactor,
    div_eq_mul_inv, Pi.mul_def, Pi.sub_def, Pi.add_def, Pi.inv_def] using
    (((hone.sub hV).mul (hone.sub hW)).mul hDi).mul
      ((((hone.mul hVi).add (hW.mul hWi)).add
        ((hE.mul hEi).mul ((hq'.mul hVi).add hW))).sub
          ((hD.mul hEi).mul (hone.add (((hq.mul hW).mul hV).mul hVi))))

theorem probePrimeLog_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b c : ProbePrime K → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (hb : ∀ P, ‖b P‖ ≤ 1) (hc : ∀ P, ‖c P‖ ≤ 1)
    (S : Finset (ProbePrime K)) (hS : probePrimeCutoff K ⊆ S)
    (P : ProbeGoodPrime K S) {x w z : E → ℂ} {t : E}
    (hx : DifferentiableAt ℂ x t) (hw : DifferentiableAt ℂ w t)
    (hz : DifferentiableAt ℂ z t)
    (ht : probeEulerRegion (x t).re (w t).re (z t).re) :
    DifferentiableAt ℂ (fun u => probePrimeLog K a b c P.val (x u, w u, z u)) t := by
  obtain ⟨hQ, hsmall, _⟩ := probeGoodPrime_norm_bounds K S hS P
  exact (Complex.differentiableAt_log
    (probePrimeCorrection_mem_slitPlane K a b c ha hb hc S hS P ht)).comp t
      (probeGoodPrimeCorrection_differentiableAt hQ hsmall
        (ha P.val) (hb P.val) (hc P.val) hx hw hz ht)

end
end ArtinMatthews
