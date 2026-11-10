module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleResidueCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine denominator clearing for the fixed-ideal residue coordinate.
The auxiliary ideal is coprime to the modulus, although the fixed class
representative itself need not be. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem idealModuleGenerator_ne_zero (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (hMtop : M ≠ ⊤) : idealModuleGenerator I M hI hM ≠ 0 := by
  intro hx
  have h := idealModuleGenerator_spec I M hI hM
  rw [hx,Ideal.span_singleton_eq_bot.mpr rfl,sup_bot_eq] at h
  have hMone : M = 1 := mul_right_cancel₀ hI (h.trans (one_mul I).symm)
  exact hMtop (hMone.trans Ideal.one_eq_top)

theorem exists_idealModule_generator_coprime_quotient
    (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (hMtop : M ≠ ⊤) :
    ∃ J : Ideal R, J ≠ ⊥ ∧ IsCoprime J M ∧
      Ideal.span {idealModuleGenerator I M hI hM} = I*J := by
  obtain ⟨J,hJ⟩ := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr (idealModuleGenerator_mem I M hI hM))
  have hx := idealModuleGenerator_ne_zero I M hI hM hMtop
  have hJ0 : J ≠ ⊥ := by
    intro hz
    rw [hz,Ideal.mul_bot,Ideal.span_singleton_eq_bot] at hJ
    exact hx hJ
  refine ⟨J,hJ0,?_,hJ⟩
  have hs := idealModuleGenerator_spec I M hI hM
  rw [hJ,mul_comm I J,← Ideal.sup_mul] at hs
  have he : M ⊔ J = 1 := mul_right_cancel₀ hI (hs.trans (one_mul I).symm)
  rw [Ideal.isCoprime_iff_sup_eq,sup_comm,he,Ideal.one_eq_top]

theorem exists_idealModule_clearing_element
    (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (hMtop : M ≠ ⊤) :
    ∃ (J : Ideal R) (t : R), J ≠ ⊥ ∧ IsCoprime J M ∧
      Ideal.span {idealModuleGenerator I M hI hM} = I*J ∧
      t ∈ J ∧ t-1 ∈ M ∧ t ≠ 0 ∧
      ∀ a : I, ∃ b : R,
        idealModuleGenerator I M hI hM*b = t*(a:R) ∧
        Ideal.Quotient.mk M b = idealResidueCoordinate I M hI hM a := by
  obtain ⟨J,hJ0,hJM,hJ⟩ := exists_idealModule_generator_coprime_quotient I M hI hM hMtop
  obtain ⟨t,ht,u,hu,htu⟩ := Ideal.isCoprime_iff_exists.mp hJM
  have ht1 : t-1 ∈ M := by
    have he : t-1 = -u := by rw [← htu]; ring
    rw [he]
    exact M.neg_mem hu
  have ht0 : t ≠ 0 := by
    intro hz
    have h1 : (1:R) ∈ M := by simpa only [hz,zero_sub,neg_neg] using M.neg_mem ht1
    exact hMtop ((Ideal.eq_top_iff_one M).mpr h1)
  refine ⟨J,t,hJ0,hJM,hJ,ht,ht1,ht0,fun a => ?_⟩
  have hta : t*(a:R) ∈ Ideal.span {idealModuleGenerator I M hI hM} := by
    rw [hJ,mul_comm I J]
    exact Ideal.mul_mem_mul ht a.property
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hta
  refine ⟨b,hb.symm,?_⟩
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (idealResidueCoordinate I M hI hM a)
  have har := (idealResidueCoordinate_eq_mk_iff I M hI hM a r).mp hr.symm
  have hdiff : t*((a:R)-r*idealModuleGenerator I M hI hM) ∈
      M * Ideal.span {idealModuleGenerator I M hI hM} := by
    have hh := Ideal.mul_mem_mul ht har
    rw [hJ]
    convert hh using 1
    ring
  obtain ⟨v,hv,hvEq⟩ := Ideal.mem_mul_span_singleton.mp hdiff
  have hcancel : b-t*r = v := by
    apply mul_right_cancel₀ (idealModuleGenerator_ne_zero I M hI hM hMtop)
    calc
      (b-t*r)*idealModuleGenerator I M hI hM =
          t*((a:R)-r*idealModuleGenerator I M hI hM) := by
        rw [mul_sub]
        linear_combination -hb
      _ = v*idealModuleGenerator I M hI hM := hvEq.symm
  have hbm : b-t*r ∈ M := hcancel.symm ▸ hv
  have htq : Ideal.Quotient.mk M t = 1 := by
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr ht1
    simpa only [map_sub,map_one,sub_eq_zero] using he
  have hbq := Ideal.Quotient.eq_zero_iff_mem.mpr hbm
  rw [map_sub,map_mul,htq,one_mul,sub_eq_zero] at hbq
  exact hbq.trans hr

theorem idealModuleClearing_principal_product
    (I J₀ J : Ideal R) (hI : I ≠ ⊥) (x a t b : R)
    (hx : Ideal.span {x} = I*J₀) (ha : Ideal.span {a} = I*J)
    (hab : x*b=t*a) :
    Ideal.span {t}*J = J₀*Ideal.span {b} := by
  have hh := congrArg (fun r : R => Ideal.span {r}) hab
  rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_mul_span_singleton,hx,ha] at hh
  apply mul_left_cancel₀ hI
  calc
    I*(Ideal.span {t}*J) = Ideal.span {t}*(I*J) := by ring
    _ = I*J₀*Ideal.span {b} := hh.symm
    _ = I*(J₀*Ideal.span {b}) := mul_assoc _ _ _

end
end ArtinMatthews.VaryingKummerAnalytic
