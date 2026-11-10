module

public import ArtinMatthews.SourceKPAllowedPositiveOrbit
public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceReflectionFieldFrequency
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

/-! Restrict a sum over all field units to its actual allowed integral
support, then split the surviving orders into squarefree and cube parts. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic SourceEulerAssembly
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "A" => allowedSubgroup K hζ S₀
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "N" => SourceNonzeroFrequency K S₀
local notation "mUnit" => sourceNonzeroFrequencyFieldUnit K S₀
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
private def allowedFrequencyOrders (n : N) : E :=
  sourceElementExponents K S₀ n.val n.property

def sourceKPPositiveCubeSupport (e : E) : Prop :=
  ∀ P, e P % 3 ≤ 1

local notation "ord" => allowedFrequencyOrders K S₀
local notation "good" => sourceKPPositiveCubeSupport K S₀

/-- The actual allowed integral field units with the indicated exterior orders. -/
def sourceKPAllowedFieldSupport (T : E → Prop) : Set Kˣ :=
  {m | m ∈ A ∧ ∃ n : N, mUnit n = m ∧ T (ord n)}

theorem sourceKPAllowedFieldSupport_mem_of_integer (T : E → Prop) (m : Kˣ) (ha : m ∈ A)
    (hI : (m : K) ∈ Set.integer (R := 𝓞 K) (↑S : Set (HeightOneSpectrum (𝓞 K))) K)
    (hT : T (sourceElementExponents K S₀ ⟨m,hI⟩
      (fun h => m.ne_zero (congrArg (fun z : sourceRing K S₀ => (z : K)) h)))) :
    m ∈ sourceKPAllowedFieldSupport K hζ S₀ T := by
  let n : N := ⟨⟨m,hI⟩, fun h => m.ne_zero (congrArg (fun z : sourceRing K S₀ => (z : K)) h)⟩
  exact ⟨ha,n,Units.ext rfl,hT⟩

private theorem fieldUnit_injective : Function.Injective mUnit := by
  intro n n' h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : Kˣ => (x : K)) h

def sourceKPAllowedSupportedFieldEquiv (T : E → Prop) :
    ({e : E // T e} × Γ) ≃ sourceKPAllowedFieldSupport K hζ S₀ T :=
  Equiv.ofBijective (fun p =>
    let n := sourceKPAllowedPositiveGammaEquiv K hζ S₀ (p.1.val,p.2)
    ⟨mUnit n.val, n.property, n.val, rfl, by
      have ho : ord n.val = p.1.val := sourceKPAllowedPositiveGammaEquiv_exponents K hζ S₀ p.1.val p.2
      rw [ho]
      exact p.1.property⟩) (by
    constructor
    · rintro ⟨e,γ⟩ ⟨e',γ'⟩ h
      let b := sourceKPAllowedPositiveGammaEquiv K hζ S₀
      have hn : (b (e.val,γ)).val = (b (e'.val,γ')).val :=
        fieldUnit_injective K S₀ (congrArg (fun m : sourceKPAllowedFieldSupport K hζ S₀ T => m.val) h)
      have he : (e.val,γ) = (e'.val,γ') := b.injective (Subtype.ext hn)
      exact Prod.ext (Subtype.ext (congrArg (fun p : E × Γ => p.1) he))
        (congrArg (fun p : E × Γ => p.2) he)
    · rintro ⟨m,hm,n,hn,hT⟩
      let n' : SourceKPAllowedPositiveFrequency K hζ S₀ := ⟨n, hn.symm ▸ hm⟩
      let b := sourceKPAllowedPositiveGammaEquiv K hζ S₀
      obtain ⟨⟨e,γ⟩,he⟩ := b.surjective n'
      have hv : (b (e,γ)).val = n := congrArg (fun z : SourceKPAllowedPositiveFrequency K hζ S₀ => z.val) he
      have hEt : T e := by
        have hx : ord (b (e,γ)).val = e := sourceKPAllowedPositiveGammaEquiv_exponents K hζ S₀ e γ
        rw [hv] at hx
        exact hx ▸ hT
      refine ⟨(⟨e,hEt⟩,γ), Subtype.ext ?_⟩
      change mUnit (b (e,γ)).val = m
      exact (congrArg mUnit hv).trans hn)

theorem sourceKPAllowedSupportedFieldEquiv_fieldUnit (T : E → Prop) (e : {e : E // T e}) (γ : Γ) :
    (sourceKPAllowedSupportedFieldEquiv K hζ S₀ T (e,γ)).val =
      gen e.val * ((sourceExteriorSixthNormOneEquiv K S).symm γ).val.val :=
  sourceKPAllowedPositiveGammaEquiv_fieldUnit K hζ S₀ e.val γ

theorem sourceKPAllowedSupportedFieldEquiv_diagonal (T : E → Prop) (e : {e : E // T e}) (γ : Γ) :
    sWholeDiagonal K S (sourceKPAllowedSupportedFieldEquiv K hζ S₀ T (e,γ)).val =
      sWholeDiagonal K S (gen e.val) * γ.val.val :=
  sourceKPAllowedPositiveGammaEquiv_diagonal K hζ S₀ e.val γ

theorem sourceKPAllowedSupportedField_hasSum (T : E → Prop) {f : Kˣ → ℂ} {z : ℂ}
    (hf : HasSum f z) (hzero : ∀ m ∉ sourceKPAllowedFieldSupport K hζ S₀ T, f m = 0) :
    HasSum (fun p : {e : E // T e} × Γ => f (sourceKPAllowedSupportedFieldEquiv K hζ S₀ T p).val) z := by
  let V := sourceKPAllowedFieldSupport K hζ S₀ T
  have hs : Function.support f ⊆ V := by
    intro m hm
    by_contra hn
    exact hm (hzero m hn)
  let g : V → ℂ := fun m => f m.val
  have hg : HasSum g z :=
    (hasSum_subtype_iff_of_support_subset (f := f) (a := z) hs).mpr hf
  let e : ({e : E // T e} × Γ) ≃ V := sourceKPAllowedSupportedFieldEquiv K hζ S₀ T
  change HasSum (g ∘ e) z
  exact (e.hasSum_iff (f := g) (a := z)).mpr hg

/-- Literal quotient and remainder by three of the exterior order vector. -/
def sourceKPPositiveSquarefreeCubeExponentsEquiv :
    (ReflectionSquarefreeExponents K S₀ × E) ≃ {e : E // good e} where
  toFun p := ⟨p.1.val + 3 • p.2, by
    intro P
    have hP := p.1.property P
    simp only [Finsupp.add_apply,Finsupp.nsmul_apply,nsmul_eq_mul]
    omega⟩
  invFun e := (⟨e.val.mapRange (· % 3) (by decide), fun P => e.property P⟩,
    e.val.mapRange (· / 3) (by decide))
  left_inv := by
    rintro ⟨c,n⟩
    apply Prod.ext
    · apply Subtype.ext
      ext P
      have hP := c.property P
      simp only [Finsupp.mapRange_apply,Finsupp.add_apply,Finsupp.nsmul_apply,nsmul_eq_mul]
      omega
    · ext P
      have hP := c.property P
      simp only [Finsupp.mapRange_apply,Finsupp.add_apply,Finsupp.nsmul_apply,nsmul_eq_mul]
      omega
  right_inv e := by
    apply Subtype.ext
    ext P
    simp only [Finsupp.mapRange_apply,Finsupp.add_apply,Finsupp.nsmul_apply,nsmul_eq_mul]
    omega

def sourceKPAllowedSquarefreeCubeFieldEquiv :
    (ReflectionSquarefreeExponents K S₀ × E) × Γ ≃ sourceKPAllowedFieldSupport K hζ S₀ good :=
  ((sourceKPPositiveSquarefreeCubeExponentsEquiv K S₀).prodCongr (Equiv.refl Γ)).trans
    (sourceKPAllowedSupportedFieldEquiv K hζ S₀ good)

theorem sourceKPAllowedSquarefreeCubeFieldEquiv_fieldUnit
    (c : ReflectionSquarefreeExponents K S₀) (n : E) (γ : Γ) :
    (sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀ ((c,n),γ)).val =
      gen (c.val + 3 • n) * ((sourceExteriorSixthNormOneEquiv K S).symm γ).val.val :=
  sourceKPAllowedSupportedFieldEquiv_fieldUnit K hζ S₀ good _ γ

theorem sourceKPAllowedSquarefreeCubeFieldEquiv_diagonal
    (c : ReflectionSquarefreeExponents K S₀) (n : E) (γ : Γ) :
    sWholeDiagonal K S (sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀ ((c,n),γ)).val =
      sWholeDiagonal K S (gen (c.val + 3 • n)) * γ.val.val :=
  sourceKPAllowedSupportedFieldEquiv_diagonal K hζ S₀ good _ γ

theorem sourceKPAllowedSquarefreeCube_mem_of_orders (m : Kˣ) (ha : m ∈ A)
    (hn : ∀ P : SourceExteriorPrime K S₀, 0 ≤ exteriorPrincipalValuation P.val m)
    (hmod : ∀ P : SourceExteriorPrime K S₀, exteriorPrincipalValuation P.val m % 3 ≤ 1) :
    m ∈ sourceKPAllowedFieldSupport K hζ S₀ good := by
  have hI := (sourceReflectionFieldUnit_mem_integer_iff K S₀ m).mpr hn
  let n : N := ⟨⟨m,hI⟩, fun h => m.ne_zero (congrArg (fun z : sourceRing K S₀ => (z : K)) h)⟩
  have hnUnit : mUnit n = m := Units.ext rfl
  refine ⟨ha,n,hnUnit,?_⟩
  intro P
  have he : exteriorPrincipalValuation P.val m = ((ord n) P : ℤ) := by
    rw [sourceExteriorPrincipalValuation_eq_neg_log]
    have hv : P.val.valuation K (m : K) = WithZero.exp (-((ord n) P : ℤ)) :=
      sourceElementExponents_valuation K S₀ hζ n.val n.property P
    rw [hv, WithZero.log_exp, neg_neg]
  have hm := hmod P
  rw [he] at hm
  omega

theorem sourceKPAllowedSquarefreeCube_hasSum {f : Kˣ → ℂ} {z : ℂ}
    (hf : HasSum f z) (hzero : ∀ m ∉ sourceKPAllowedFieldSupport K hζ S₀ good, f m = 0) :
    HasSum (fun p : (ReflectionSquarefreeExponents K S₀ × E) × Γ =>
      f (sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀ p).val) z := by
  let g (p : {e : E // good e} × Γ) := f (sourceKPAllowedSupportedFieldEquiv K hζ S₀ good p).val
  have hg : HasSum g z := sourceKPAllowedSupportedField_hasSum K hζ S₀ good hf hzero
  let e := (sourceKPPositiveSquarefreeCubeExponentsEquiv K S₀).prodCongr (Equiv.refl Γ)
  change HasSum (g ∘ e) z
  exact (e.hasSum_iff (f := g) (a := z)).mpr hg

end
end ArtinMatthews
