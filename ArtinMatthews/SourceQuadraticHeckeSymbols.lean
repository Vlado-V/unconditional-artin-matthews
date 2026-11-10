module

public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SIntegerSexticReciprocity
public import ArtinMatthews.SourcePrimeExponentProducts
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SIntegerQuotient SIntegerTameSymbol VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "OS" => PrincipalIntegerRing T
local notation "E" => SourcePrimeExponents F S₀
local notation "Pext" => SourceExteriorPrime F S₀
local notation "a" => (sourceAllowedPrimeGenerator F hζ S₀ : Pext → OS)
local notation "ha" => sourceAllowedPrimeGenerator_ideal F hζ S₀

private def sourceSexticPrimeValue (P : Pext) : OS →* ℂ :=
  (reflectionPrimeCharacters F hζ S₀ P).toMonoidHom.comp
    (((generatorResidueEquiv T P.val P.property (a P) (ha P)).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.span {a P} : Ideal OS))).toMonoidHom)

private theorem sourceSexticPrimeValue_symmetric (P Q : Pext) :
    sourceSexticPrimeValue F S₀ hζ P (a Q) = sourceSexticPrimeValue F S₀ hζ Q (a P) := by
  by_cases h : P = Q
  · subst Q
    rfl
  · exact sourceAngularResidue_reciprocity F hζ S₀ P.val Q.val
      (fun he => h (Subtype.ext he)) P.property Q.property (a P) (a Q) (ha P) (ha Q)
      (sourceAllowedPrimeUnit_allowed F hζ S₀ P) (sourceAllowedPrimeUnit_allowed F hζ S₀ Q)

private theorem sourcePrimeExponentLocalWeight_eq_primeValue (P : Pext)
    (n : ℕ) (hn : 0 < n) (x : OS) :
    sourcePrimeExponentLocalWeight F hζ S₀ (reflectionPrimeCharacters F hζ S₀) P n x =
      (sourceSexticPrimeValue F S₀ hζ P x) ^ n := by
  let χ := reflectionPrimeCharacters F hζ S₀ P
  let b : OS := a P
  let I : Ideal OS := Ideal.span {b ^ n}
  have he := Ideal.quotEquivOfEq_mk (R := OS) (generator_power_ideal T P.val b (ha P) n) x
  change generatorPowerWeight T P.val P.property b (ha P) χ n
    ((Ideal.quotEquivOfEq (generator_power_ideal T P.val b (ha P) n))
      (Ideal.Quotient.mk (primePowerIdeal T P.val n) x)) = _
  refine (congrArg (generatorPowerWeight T P.val P.property b (ha P) χ n) he).trans ?_
  change generatorPowerWeight T P.val P.property b (ha P) χ n (Ideal.Quotient.mk I x) = _
  change (if h : 0 < n then
    (generatorResidueCharacter T P.val P.property b (ha P) χ ^ n)
      (generatorResidueReduction T b n h (Ideal.Quotient.mk I x)) else 1) = _
  let χ' := generatorResidueCharacter T P.val P.property b (ha P) χ
  let z := generatorResidueReduction T b n hn (Ideal.Quotient.mk I x)
  calc
    _ = (χ' ^ n) z := dite_eq_left hn
    _ = χ' z ^ n := MulChar.pow_apply' χ' hn.ne' z
    _ = χ' (Ideal.Quotient.mk (Ideal.span {b} : Ideal OS) x) ^ n :=
      congrArg (fun y => χ' y ^ n) (generatorResidueReduction_mk T b n hn x)
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sourceReflectionExponentResidueValue_eq_primeProduct (e f : E) :
    reflectionExponentResidueValue F hζ S₀ e (sourcePrimeExponentGenerator F hζ S₀ f) =
      ∏ P ∈ e.support, ∏ Q ∈ f.support, (sourceSexticPrimeValue F S₀ hζ P (a Q)) ^ (e P * f Q) := by
  unfold reflectionExponentResidueValue sourcePrimeExponentWeight Finsupp.prod
  apply Finset.prod_congr rfl
  intro P hP
  change sourcePrimeExponentLocalWeight F hζ S₀ (reflectionPrimeCharacters F hζ S₀)
    P (e P) (sourcePrimeExponentGenerator F hζ S₀ f) = _
  rw [sourcePrimeExponentLocalWeight_eq_primeValue F S₀ hζ P (e P)
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP))]
  let g := sourceSexticPrimeValue F S₀ hζ P
  change (g (∏ Q ∈ f.support, a Q ^ f Q)) ^ e P = _
  rw [map_prod, ← Finset.prod_pow f.support (e P) (fun Q => g (a Q ^ f Q))]
  apply Finset.prod_congr rfl
  intro Q _
  rw [map_pow, ← pow_mul, Nat.mul_comm]

/-- Reciprocity of the actual residue values for the fixed product generators.
The products include the zero extension when the supports meet. -/
theorem sourceReflectionExponentResidueValue_symmetric (e f : E) :
    reflectionExponentResidueValue F hζ S₀ e (sourcePrimeExponentGenerator F hζ S₀ f) =
      reflectionExponentResidueValue F hζ S₀ f (sourcePrimeExponentGenerator F hζ S₀ e) := by
  rw [sourceReflectionExponentResidueValue_eq_primeProduct,
    sourceReflectionExponentResidueValue_eq_primeProduct]
  calc
    _ = ∏ P ∈ e.support, ∏ Q ∈ f.support,
        (sourceSexticPrimeValue F S₀ hζ Q (a P)) ^ (f Q * e P) := by
      apply Finset.prod_congr rfl
      intro P _
      apply Finset.prod_congr rfl
      intro Q _
      rw [sourceSexticPrimeValue_symmetric F S₀ hζ P Q, Nat.mul_comm]
    _ = _ := Finset.prod_comm

/-- The cube in the literal reflected quadratic kernel is symmetric. -/
theorem sourceReflectionQuadraticSymbol_reciprocity (e f : E) :
    reflectionExponentResidueValue F hζ S₀ e (sourcePrimeExponentGenerator F hζ S₀ f) ^ 3 =
      reflectionExponentResidueValue F hζ S₀ f (sourcePrimeExponentGenerator F hζ S₀ e) ^ 3 :=
  congrArg (fun z : ℂ => z ^ 3) (sourceReflectionExponentResidueValue_symmetric F S₀ hζ e f)

private theorem sourceSexticPrimeValue_ne_zero_iff (P Q : Pext) :
    sourceSexticPrimeValue F S₀ hζ P (a Q) ≠ 0 ↔ P ≠ Q := by
  let I : Ideal OS := Ideal.span {a P}
  let Eres := generatorResidueEquiv T P.val P.property (a P) (ha P)
  let : Field ((𝓞 F) ⧸ P.val.asIdeal) := Ideal.Quotient.field _
  change reflectionPrimeCharacters F hζ S₀ P (Eres (Ideal.Quotient.mk I (a Q))) ≠ 0 ↔ P ≠ Q
  rw [MulChar.apply_ne_zero_iff, isUnit_iff_ne_zero, Eres.map_ne_zero_iff]
  constructor
  · intro h hp
    subst Q
    exact h (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
  · intro h hzero
    have hm : a Q ∈ P.val.asIdeal.map (algebraMap (𝓞 F) OS) :=
      (ha P).symm ▸ Ideal.Quotient.eq_zero_iff_mem.mp hzero
    exact primeGenerator_other_avoids F T P.val Q.val (fun he => h (Subtype.ext he))
      P.property (a Q) (ha Q) hm

/-- The actual quadratic exterior symbol has exactly the shared-prime zero mask. -/
theorem sourceReflectionQuadraticSymbol_ne_zero_iff (e f : E) :
    reflectionExponentResidueValue F hζ S₀ e (sourcePrimeExponentGenerator F hζ S₀ f) ^ 3 ≠ 0 ↔
      Disjoint e.support f.support := by
  rw [sourceReflectionExponentResidueValue_eq_primeProduct, pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)]
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro P he hf
    have hi := (Finset.prod_ne_zero_iff.mp h) P he
    have hj := (Finset.prod_ne_zero_iff.mp hi) P hf
    have hp : e P * f P ≠ 0 :=
      Nat.mul_ne_zero (Finsupp.mem_support_iff.mp he) (Finsupp.mem_support_iff.mp hf)
    exact (sourceSexticPrimeValue_ne_zero_iff F S₀ hζ P P).mp
      ((pow_ne_zero_iff hp).mp hj) rfl
  · intro h
    refine Finset.prod_ne_zero_iff.mpr fun P he => Finset.prod_ne_zero_iff.mpr fun Q hf => ?_
    have hne : P ≠ Q := fun h' => Finset.disjoint_left.mp h he (h' ▸ hf)
    exact pow_ne_zero _ ((sourceSexticPrimeValue_ne_zero_iff F S₀ hζ P Q).mpr hne)

set_option backward.isDefEq.respectTransparency false in
theorem sourceReflectionExponentResidueValue_mul (e : E) (x y : OS) :
    reflectionExponentResidueValue F hζ S₀ e (x * y) =
      reflectionExponentResidueValue F hζ S₀ e x *
        reflectionExponentResidueValue F hζ S₀ e y := by
  unfold reflectionExponentResidueValue sourcePrimeExponentWeight Finsupp.prod
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  have hp := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP)
  change sourcePrimeExponentLocalWeight F hζ S₀ (reflectionPrimeCharacters F hζ S₀)
    P (e P) (x * y) = _
  simp only [sourcePrimeExponentLocalWeight_eq_primeValue F S₀ hζ P (e P) hp, map_mul, mul_pow]

set_option backward.isDefEq.respectTransparency false in
/-- The quadratic kernel is multiplicative in the ideal indexing its character. -/
theorem sourceReflectionQuadraticSymbol_add_left (e e' f : E) :
    reflectionExponentResidueValue F hζ S₀ (e + e') (sourcePrimeExponentGenerator F hζ S₀ f) ^ 3 =
      (reflectionExponentResidueValue F hζ S₀ e (sourcePrimeExponentGenerator F hζ S₀ f) ^ 3) *
      (reflectionExponentResidueValue F hζ S₀ e' (sourcePrimeExponentGenerator F hζ S₀ f) ^ 3) := by
  have hmul := sourceReflectionExponentResidueValue_mul F S₀ hζ f
    (sourcePrimeExponentGenerator F hζ S₀ e) (sourcePrimeExponentGenerator F hζ S₀ e')
  rw [sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ (e + e') f,
    sourcePrimeExponentGenerator_add, hmul, mul_pow]
  rw [sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ f e,
    sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ f e']

private theorem sourceSexticPrimeValue_norm_eq_one (P Q : Pext) (hPQ : P ≠ Q) :
    ‖sourceSexticPrimeValue F S₀ hζ P (a Q)‖ = 1 := by
  let I : Ideal OS := Ideal.span {a P}
  let χ := reflectionPrimeCharacters F hζ S₀ P
  let x := generatorResidueEquiv T P.val P.property (a P) (ha P) (Ideal.Quotient.mk I (a Q))
  have hn : χ x ≠ 0 := (sourceSexticPrimeValue_ne_zero_iff F S₀ hζ P Q).mpr hPQ
  have hu : IsUnit x := MulChar.apply_ne_zero_iff.mp hn
  let : Finite ((𝓞 F) ⧸ P.val.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
  let := Fintype.ofFinite ((𝓞 F) ⧸ P.val.asIdeal)ˣ
  obtain ⟨u, hu⟩ := hu
  change ‖χ x‖ = 1
  rw [← hu]
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem sourceReflectionQuadraticSymbol_norm_eq_one (e f : E)
    (h : Disjoint e.support f.support) :
    ‖reflectionExponentResidueValue F hζ S₀ e (sourcePrimeExponentGenerator F hζ S₀ f) ^ 3‖ = 1 := by
  rw [sourceReflectionExponentResidueValue_eq_primeProduct, norm_pow, norm_prod]
  have he : (∏ P ∈ e.support,
      ‖∏ Q ∈ f.support, (sourceSexticPrimeValue F S₀ hζ P (a Q)) ^ (e P * f Q)‖) = 1 := by
    apply Finset.prod_eq_one
    intro P hP
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro Q hQ
    have hne : P ≠ Q := fun h' => Finset.disjoint_left.mp h hP (h' ▸ hQ)
    rw [norm_pow, sourceSexticPrimeValue_norm_eq_one F S₀ hζ P Q hne, one_pow]
  rw [he, one_pow]

end
end ArtinMatthews.SourceEulerAssembly
