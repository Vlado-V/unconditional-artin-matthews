module

public import OAI.NumberTheory.PrimePackets.IdealCoefficients
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishingProducts
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Geometry.Euclidean.Projection


set_option backward.privateInPublic true
@[expose] public section

/-! Actual prime-ideal local Euler factors, extracted from the general
PrimePackets/PrimeSums and RootOverlaps proofs. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Finset UniqueFactorizationMonoid
open OAI.PrimeDegreePackets
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
variable (K : Type*) [Field K] [NumberField K]

lemma idealsOverPrime_prime {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : Prime P :=
  UniqueFactorizationMonoid.prime_of_normalized_factor _ (Multiset.mem_toFinset.mp hP)

lemma idealsOverPrime_norm_power {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : ∃ e : ℕ, Ideal.absNorm P = p^e := by
  have HD : Ideal.absNorm P ∣ Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) :=
    map_dvd Ideal.absNorm (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))
  rw [Ideal.absNorm_span_natCast] at HD
  obtain ⟨e,-,he⟩ := (Nat.dvd_prime_pow hp).mp HD
  exact ⟨e,he⟩

 
def PrimaryIdeal (p : ℕ) :=
  {I : Ideal (𝓞 K) // I ≠ 0 ∧ ∀ P ∈ normalizedFactors I, P ∈ idealsOverPrime K p}

lemma primary_ideal_norm_power {p : ℕ} (hp : p.Prime) (I : PrimaryIdeal K p) :
    ∃ e : ℕ, Ideal.absNorm I.1 = p^e := by
  have HI := Ideal.prod_normalizedFactors_eq_self I.2.1
  rw [←HI, map_multiset_prod]
  have HA : ∀ m : Multiset (Ideal (𝓞 K)),
      (∀ P ∈ m, P ∈ idealsOverPrime K p) →
      ∃e : ℕ, (m.map Ideal.absNorm).prod = p^e := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0,by simp⟩
    | @cons P m ih =>
      intro hm
      obtain ⟨e,he⟩ := idealsOverPrime_norm_power K hp (hm P (by simp))
      obtain ⟨f,hf⟩ := ih (fun Q hQ => hm Q (Multiset.mem_cons_of_mem hQ))
      exact ⟨e+f,by simp [he,hf,pow_add]⟩
  exact HA _ I.2.2

 

def primaryIdealMultisetEquiv (p : ℕ) :
    Multiset (idealsOverPrime K p) ≃ PrimaryIdeal K p := by
  classical
  let F (m : Multiset (idealsOverPrime K p)) := (m.map Subtype.val).prod
  have hfac (m : Multiset (idealsOverPrime K p)) :
      normalizedFactors (F m) = m.map Subtype.val := by
    apply normalizedFactors_prod_of_prime
    intro P hP
    obtain ⟨Q,-,rfl⟩ := Multiset.mem_map.mp hP
    exact idealsOverPrime_prime K Q.2
  have hF (m : Multiset (idealsOverPrime K p)) : F m ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hP
    obtain ⟨Q,-,hQ⟩ := Multiset.mem_map.mp hP
    exact (idealsOverPrime_prime K Q.2).ne_zero hQ
  let f (m : Multiset (idealsOverPrime K p)) : PrimaryIdeal K p :=
    ⟨F m,hF m,by
      intro P hP
      rw [hfac] at hP
      obtain ⟨Q,-,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro m l h
    have H := congrArg (fun I : PrimaryIdeal K p => normalizedFactors I.1) h
    change normalizedFactors (F m) = normalizedFactors (F l) at H
    rw [hfac,hfac] at H
    exact Multiset.map_injective Subtype.val_injective H
  · intro I
    let m : Multiset (idealsOverPrime K p) :=
      (normalizedFactors I.1).attach.map (fun P => ⟨P.1,I.2.2 P.1 P.2⟩)
    refine ⟨m,Subtype.ext ?_⟩
    change ((normalizedFactors I.1).attach.map _ |>.map Subtype.val).prod = I.1
    simp only [Multiset.map_map,Function.comp_def,Multiset.attach_map_val]
    exact Ideal.prod_normalizedFactors_eq_self I.2.1

 

def primaryIdealNormEquiv (p : ℕ) (hp : p.Prime) :
    (Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) ≃ PrimaryIdeal K p := by
  classical
  let f (a : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) : PrimaryIdeal K p :=
    ⟨a.2.1,by
      intro hz
      have H := a.2.2
      rw [hz,_root_.map_zero] at H
      exact (pow_ne_zero _ hp.ne_zero) H.symm,
      fun P hP => ideal_factor_mem_over K hp a.2.2 hP⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨e,I⟩ ⟨d,J⟩ he
    have hIJ : I.1 = J.1 := congrArg (fun I : PrimaryIdeal K p => I.1) he
    have hed : p^e = p^d := by rw [←I.2,←J.2,hIJ]
    have hed' := (Nat.pow_right_injective hp.two_le) hed
    subst d
    exact congrArg (Sigma.mk e) (Subtype.ext hIJ)
  · intro I
    obtain ⟨e,he⟩ := primary_ideal_norm_power K hp I
    exact ⟨⟨e,⟨I.1,he⟩⟩,Subtype.ext rfl⟩

@[simp] lemma primaryIdealMultisetEquiv_val (p : ℕ) (m : Multiset (idealsOverPrime K p)) :
    (primaryIdealMultisetEquiv K p m).val = (m.map Subtype.val).prod := rfl

@[simp] lemma primaryIdealNormEquiv_val (p : ℕ) (hp : p.Prime)
    (I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) :
    (primaryIdealNormEquiv K p hp I).val = I.2.val := rfl


lemma idealsOverPrime_norm_two_le {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ idealsOverPrime K p) : 2 ≤ Ideal.absNorm P := by
  have hP0 : Ideal.absNorm P ≠ 0 := by
    exact fun he => (idealsOverPrime_prime K hP).ne_zero (Ideal.absNorm_eq_zero_iff.mp he)
  have hP1 : Ideal.absNorm P ≠ 1 := by
    intro he
    have := Ideal.absNorm_eq_one_iff.mp he
    exact (idealsOverPrime_prime K hP).not_isUnit (by simp [this])
  omega

 


lemma zetaSummand_norm_lt_one {s : ℂ} (hs : 1 < s.re) {m : ℕ} (hm : 2 ≤ m) :
    ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) m‖ < 1 := by
  change ‖(m : ℂ)^(-s)‖ < 1
  rw [←Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg m)
      (Complex.re_neg_ne_zero_of_one_lt_re hs),Complex.neg_re]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hm
  · linarith

lemma primary_ideal_complex_series {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    Summable (fun I : PrimaryIdeal K p =>
      ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)‖) ∧
    (∑' I : PrimaryIdeal K p,
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)) =
      ∏ P : idealsOverPrime K p,
        (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  have HM (m : Multiset (idealsOverPrime K p)) :
      H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1) =
        (m.map (fun P => H (Ideal.absNorm P.1))).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons P m ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,map_mul]
      exact congrArg (fun z => H (Ideal.absNorm P.1)*z) ih
  obtain ⟨hS,hT⟩ := complex_tsum_multiset_prod
    (fun P : idealsOverPrime K p => H (Ideal.absNorm P.1))
    (fun P => zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2))
  constructor
  · rw [←(primaryIdealMultisetEquiv K p).summable_iff]
    change Summable (fun m => ‖H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1)‖)
    simpa only [HM] using hS
  · rw [←(primaryIdealMultisetEquiv K p).tsum_eq]
    exact (tsum_congr HM).trans hT

lemma norm_fiber_complex_tsum (m : ℕ) (hm : m ≠ 0) (F : ℕ → ℂ) :
    (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m}, F (Ideal.absNorm I.1)) =
      (idealCoefficient K m : ℂ) * F m := by
  classical
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
    (Ideal.finite_setOfPred_absNorm_eq _).to_subtype
  let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
  have he : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} => F (Ideal.absNorm I.1)) =
      (fun _ => F m) := funext (fun I => congrArg F I.2)
  rw [he,tsum_fintype,sum_const,idealCoefficient_pos K m hm,Nat.card_eq_fintype_card,
    nsmul_eq_mul,Finset.card_univ]

lemma primary_ideal_tsum_by_norm {p : ℕ} (hp : p.Prime) (H : ℕ → ℂ)
    (HS : Summable (fun I : PrimaryIdeal K p => H (Ideal.absNorm I.1))) :
    (∑' I : PrimaryIdeal K p, H (Ideal.absNorm I.1)) =
      ∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) * H (p^e) := by
  have HE : Summable (fun I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} =>
      H (Ideal.absNorm I.2.1)) :=
    (primaryIdealNormEquiv K p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.2.1) :=
      ((primaryIdealNormEquiv K p hp).tsum_eq (fun I => H (Ideal.absNorm I.1))).symm
    _ = ∑' e : ℕ, ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.1) := HE.tsum_sigma
    _ = _ := tsum_congr (fun e => norm_fiber_complex_tsum K _ (pow_ne_zero _ hp.ne_zero) H)

lemma ideal_local_complex_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) *
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (p^e)) =
        ∏ P : idealsOverPrime K p,
          (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  have HD := primary_ideal_complex_series K hs (p := p)
  exact (primary_ideal_tsum_by_norm K hp _ HD.1.of_norm).symm.trans HD.2

end
end ArtinMatthews.VaryingKummerAnalytic
