module

public import ArtinMatthews.SourceReflectionPositiveTwistResidue
public import ArtinMatthews.SourceKPCuspResidualFourierUpper
public import ArtinMatthews.SourceKPTraceJacquetFiniteFiber


set_option backward.privateInPublic true
@[expose] public section

/-! The positive average is the actual finite upper translation at
every prime in the row support. The finite-upper phase separates on
that support, so local inversion applies before any retained cutoff. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "E" => SourcePrimeExponents K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ

abbrev SourceReflectionPositiveTwistLabels (e : E) :=
  (P : e.support) → (𝓞 K) ⧸ P.val.val.asIdeal

local instance positiveTwistResidueFinite (P : SourceExteriorPrime K S₀) :
    Finite ((𝓞 K) ⧸ P.val.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot

local instance positiveTwistResidueFintype (P : SourceExteriorPrime K S₀) :
    Fintype ((𝓞 K) ⧸ P.val.asIdeal) := Fintype.ofFinite _

local instance positiveTwistLabelFintype (e : E) :
    Fintype (SourceReflectionPositiveTwistLabels K S₀ e) := by
  letI (P : e.support) : Fintype ((𝓞 K) ⧸ P.val.val.asIdeal) :=
    positiveTwistResidueFintype K S₀ P.val
  infer_instance

def sourceReflectionPositiveTwistWeight (e : E) (u : SourceReflectionPositiveTwistLabels K S₀ e) : ℂ :=
  ∏ P : e.support, sourceReflectionTameFourierCoefficient K hζ S₀ P.val
    (sourceReflectionPositiveIndex (e P.val)) (u P)

def sourceReflectionPositiveTwistAdele (e : E) (u : SourceReflectionPositiveTwistLabels K S₀ e) : 𝔸ᶠ[K] :=
  sourceKPExteriorUpperAdele K S₀ e.support
    (fun P => sourceReflectionPositiveLocalTranslation K hζ S₀ P.val (u P))

theorem sourceReflectionExteriorUpperAdele_mul_frequency
    (F : Finset (SourceExteriorPrime K S₀)) (m : Kˣ)
    (x : (P : F) → P.val.val.adicCompletion K) :
    algebraMap K 𝔸ᶠ[K] (m:K) * sourceKPExteriorUpperAdele K S₀ F x =
      sourceKPExteriorUpperAdele K S₀ F
        (fun P => (sourceKPTraceJacquetFrequencyAt K P.val.val m : P.val.val.adicCompletion K) * x P) := by
  unfold sourceKPExteriorUpperAdele
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  let p := P.val.val
  let y := (sourceKPTraceJacquetFrequencyAt K p m : p.adicCompletion K)*x P
  apply FiniteAdeleRing.ext
  intro Q
  change (algebraMap K 𝔸ᶠ[K] (m:K)) Q * sourceKPFiniteAdditiveSingle K p (x P) Q =
    sourceKPFiniteAdditiveSingle K p y Q
  by_cases he : Q = p
  · subst Q
    rw [sourceKPFiniteAdditiveSingle_same, sourceKPFiniteAdditiveSingle_same,
      FiniteAdeleRing.algebraMap_apply] <;> rfl
  · rw [sourceKPFiniteAdditiveSingle_other K p (x P) Q he,
      sourceKPFiniteAdditiveSingle_other K p y Q he, mul_zero]

theorem sourceReflectionPositiveTwistAdele_character
    (e : E) (m : Kˣ) (x : (P : e.support) → sourceJacquetIntegers K P.val.val)
    (hx : ∀ P : e.support, (x P : P.val.val.adicCompletion K) =
      (sourceKPTraceJacquetFrequencyAt K P.val.val m : P.val.val.adicCompletion K))
    (u : SourceReflectionPositiveTwistLabels K S₀ e) :
    finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K) *
      sourceReflectionPositiveTwistAdele K hζ S₀ e u) =
        ∏ P : e.support, localFiniteCharacter K P.val.val ((x P : P.val.val.adicCompletion K) *
          sourceReflectionPositiveLocalTranslation K hζ S₀ P.val (u P)) := by
  rw [sourceReflectionPositiveTwistAdele, sourceReflectionExteriorUpperAdele_mul_frequency K S₀,
    sourceKPExteriorUpperAdele_character]
  apply Finset.prod_congr rfl
  intro P _
  exact congrArg (fun z : P.val.val.adicCompletion K => localFiniteCharacter K P.val.val
    (z * sourceReflectionPositiveLocalTranslation K hζ S₀ P.val (u P))) (hx P).symm

def sourceReflectionPositiveFiniteTwist (e : E) (W : Gf → ℂ) (qf : Gf) : ℂ :=
  ∑ u : SourceReflectionPositiveTwistLabels K S₀ e,
    sourceReflectionPositiveTwistWeight K hζ S₀ e u *
      W (Nf (sourceReflectionPositiveTwistAdele K hζ S₀ e u) * qf)

theorem sourceReflectionPositiveFiniteTwist_eq_product
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : E) (m : Kˣ)
    (x : (P : e.support) → sourceJacquetIntegers K P.val.val)
    (hx : ∀ P : e.support, (x P : P.val.val.adicCompletion K) =
      (sourceKPTraceJacquetFrequencyAt K P.val.val m : P.val.val.adicCompletion K))
    (W : Gf → ℂ) (qf : Gf)
    (hW : ∀ u : 𝔸ᶠ[K], W (Nf u*qf) =
      finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K)*u)*W qf) :
    sourceReflectionPositiveFiniteTwist K hζ S₀ e W qf =
      (∏ P : e.support, (reflectionPrimeCharacters K hζ S₀ P.val ^
        (sourceReflectionPositiveIndex (e P.val)).val :
          MulChar ((𝓞 K) ⧸ P.val.val.asIdeal) ℂ)
            (sourceJacquetReduction K P.val.val (x P))) * W qf := by
  let f (P : e.support) (a : (𝓞 K) ⧸ P.val.val.asIdeal) :=
    sourceReflectionTameFourierCoefficient K hζ S₀ P.val (sourceReflectionPositiveIndex (e P.val)) a *
      localFiniteCharacter K P.val.val ((x P : P.val.val.adicCompletion K) *
        sourceReflectionPositiveLocalTranslation K hζ S₀ P.val a)
  have h (u : SourceReflectionPositiveTwistLabels K S₀ e) :
      sourceReflectionPositiveTwistWeight K hζ S₀ e u *
        W (Nf (sourceReflectionPositiveTwistAdele K hζ S₀ e u)*qf) =
      (∏ P : e.support, f P (u P)) * W qf := by
    rw [hW, sourceReflectionPositiveTwistAdele_character K hζ S₀ e m x hx,
      ← mul_assoc, sourceReflectionPositiveTwistWeight, ← Finset.prod_mul_distrib]
  unfold sourceReflectionPositiveFiniteTwist
  simp_rw [h]
  rw [← Finset.sum_mul, ← Fintype.prod_sum f]
  apply congrArg (fun a : ℂ => a * W qf)
  apply Finset.prod_congr rfl
  intro P _
  exact sourceReflectionPositiveLocalFourier K hζ S₀ P.val hS
    (sourceReflectionPositiveIndex (e P.val)) (x P)

theorem sourceReflectionPositiveFiniteTwist_eq_residueValue
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : E) (m : Kˣ)
    (x : sourceRing K S₀) (hx : (m:K) = (x:K)) (W : Gf → ℂ) (qf : Gf)
    (hW : ∀ u : 𝔸ᶠ[K], W (Nf u*qf) =
      finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K)*u)*W qf) :
    sourceReflectionPositiveFiniteTwist K hζ S₀ e W qf =
      reflectionExponentResidueValue K hζ S₀ e x * W qf := by
  let y (P : e.support) := sourceReflectionPositiveSIntegerAt K S₀ P.val x
  have hy (P : e.support) : (y P : P.val.val.adicCompletion K) =
      (sourceKPTraceJacquetFrequencyAt K P.val.val m : P.val.val.adicCompletion K) := by
    change algebraMap K (P.val.val.adicCompletion K) (x:K) = algebraMap K _ (m:K)
    rw [hx]
  rw [sourceReflectionPositiveFiniteTwist_eq_product K hζ S₀ hS e m y hy W qf hW]
  apply congrArg (fun a : ℂ => a * W qf)
  unfold reflectionExponentResidueValue sourcePrimeExponentWeight Finsupp.prod
  let f (P : SourceExteriorPrime K S₀) :=
    (reflectionPrimeCharacters K hζ S₀ P ^ (sourceReflectionPositiveIndex (e P)).val :
      MulChar ((𝓞 K) ⧸ P.val.asIdeal) ℂ)
      (sourceJacquetReduction K P.val (sourceReflectionPositiveSIntegerAt K S₀ P x))
  change (∏ P : e.support, f P.val) = _
  rw [Finset.prod_coe_sort e.support f]
  apply Finset.prod_congr rfl
  intro P hP
  exact sourceReflectionPositiveLocalWeight_eq K hζ S₀ P (e P)
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hP)) x

theorem sourceReflectionPositiveFiniteTwist_fourierValue
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (e : E) (m : Kˣ)
    (x : sourceRing K S₀) (hx : (m:K) = (x:K))
    {T : ℝ} (hT : 1 ≤ T) (qf : Gf) :
    sourceReflectionPositiveFiniteTwist K hζ S₀ e
      (sourceKPCuspResidualFourierValue K hζ m hT) qf =
      reflectionExponentResidueValue K hζ S₀ e x * sourceKPCuspResidualFourierValue K hζ m hT qf :=
  sourceReflectionPositiveFiniteTwist_eq_residueValue K hζ S₀ hS e m x hx _ qf
    (sourceKPCuspResidualFourierValue_left_finite_upper K hζ m hT qf)

end
end ArtinMatthews
