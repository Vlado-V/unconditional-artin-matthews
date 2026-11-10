module

public import ArtinMatthews.SourceKPAdeleLocalEmbedding
public import ArtinMatthews.SourceKPExteriorTensorUpper
public import ArtinMatthews.SourceKPAdelicUpper
import ArtinMatthews.SourceAdelicIwasawaAssembly
public import ArtinMatthews.SourceKubotaGL2Generation
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The finite exterior upper tuple is the canonical full adelic
upper lift of its actual supported sum. Its Whittaker character
is the actual standard finite additive character of that sum. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic Matrix Matrix.GeneralLinearGroup
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical BigOperators TensorProduct AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteAdditiveSingle (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K) : 𝔸ᶠ[K] :=
  RestrictedProduct.single (fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletionIntegers K) P x

theorem sourceKPAdeleSingleMatrix_upper (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K) :
    sourceKPAdeleSingleMatrix K P (sourceGL2Upper x) =
      sourceKPUpperMatrix 𝔸ᶠ[K] (sourceKPFiniteAdditiveSingle K P x) := by
  apply sourceKPAdeleMatrixAt_ext K
  intro Q
  rw [sourceKPAdeleMatrixAt_upper]
  by_cases hQP : Q = P
  · subst Q
    rw [sourceKPAdeleSingleMatrix_same]
    congr 1
    exact (RestrictedProduct.single_eq_same _ P x).symm
  · rw [sourceKPAdeleSingleMatrix_other K P Q hQP]
    have hz : sourceKPFiniteAdditiveSingle K P x Q = 0 :=
      RestrictedProduct.single_eq_of_ne _ x hQP
    rw [hz, sourceGL2Upper_zero]

theorem sourceKPAdelicLocalProjective_upper (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K) :
    sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x)) =
        sourceKPAdelicUpperLift K hζ (0, sourceKPFiniteAdditiveSingle K P x) := by
  apply Prod.ext
  · change 1 = ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) 0)
    rw [sourceKPUpperMatrix_zero, map_one]
  · change sourceKPFiniteAdeleProjectiveMk K hζ
        (sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2Lift K hζ P (sourceGL2Upper x))) =
      sourceKPFiniteAdeleProjectiveMk K hζ
        ⟨1, sourceKPUpperMatrix 𝔸ᶠ[K] (sourceKPFiniteAdditiveSingle K P x)⟩
    apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
    apply SourceKPFiniteAdeleCover.ext
    · change (sourceKPRootsTransport K hζ P).symm (1 / sourceKPFinitePhase K hζ P (sourceGL2Upper x)) = 1
      rw [sourceKPFinitePhase_upper, div_one, map_one]
    · exact sourceKPAdeleSingleMatrix_upper K P x

def sourceKPFiniteUpperHom : Multiplicative 𝔸ᶠ[K] →* SourceKPAdelicProjective K hζ where
  toFun x := sourceKPAdelicUpperLift K hζ (0, x.toAdd)
  map_one' := sourceKPAdelicUpperLift_zero K hζ
  map_mul' x y := by
    have he : ((0, (x * y).toAdd) : 𝔸[K]) = (0, x.toAdd) + (0, y.toAdd) := by
      apply Prod.ext
      · exact (zero_add 0).symm
      · rfl
    change sourceKPAdelicUpperLift K hζ (0, (x * y).toAdd) = _
    rw [he]
    exact sourceKPAdelicUpperLift_add K hζ _ _

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (SourceExteriorPrime K S₀))

def sourceKPExteriorUpperAdele (x : (P : T) → P.val.val.adicCompletion K) : 𝔸ᶠ[K] :=
  ∑ P : T, sourceKPFiniteAdditiveSingle K P.val.val (x P)

theorem sourceKPAdelicFiniteProduct_upper (x : (P : T) → P.val.val.adicCompletion K) :
    sourceKPAdelicFiniteProduct K hζ S₀ T (sourceKPExteriorUpperTuple K hζ S₀ T x) =
      sourceKPAdelicUpperLift K hζ (0, sourceKPExteriorUpperAdele K S₀ T x) := by
  let u (P : T) : Multiplicative 𝔸ᶠ[K] := Multiplicative.ofAdd (sourceKPFiniteAdditiveSingle K P.val.val (x P))
  let f := sourceKPFiniteUpperHom K hζ
  let g (P : T) := sourceKPAdelicLocalProjective K hζ P.val.val
    (sourceFiniteKP2ProjectiveLift K hζ P.val.val (sourceGL2Upper (x P)))
  have hg : Set.Pairwise (↑(Finset.univ : Finset T)) (fun P Q => Commute (g P) (g Q)) := by
    intro P _ Q _ hPQ
    exact sourceKPAdelicLocalProjective_commute K hζ P.val.val Q.val.val
      (fun h => hPQ (Subtype.ext (Subtype.ext h.symm))) _ _
  change Finset.univ.noncommProd g hg = _
  calc
    _ = Finset.univ.noncommProd (fun P : T => f (u P))
          (by intro P _ Q _ _; exact (Commute.all (u P) (u Q)).map f) := by
      apply Finset.noncommProd_congr
      · rfl
      · intro P _
        exact sourceKPAdelicLocalProjective_upper K hζ P.val.val (x P)
    _ = f (Finset.univ.noncommProd u (by intro P _ Q _ _; exact Commute.all _ _)) :=
      (Finset.map_noncommProd _ u _ f).symm
    _ = _ := by
      rw [Finset.noncommProd_eq_prod]
      change sourceKPAdelicUpperLift K hζ (0, (∏ P : T, u P).toAdd) = _
      rw [toAdd_prod]
      rfl

theorem sourceKPExteriorUpperAdele_character (x : (P : T) → P.val.val.adicCompletion K) :
    finiteCharacter K (sourceKPExteriorUpperAdele K S₀ T x) =
      ∏ P : T, localFiniteCharacter K P.val.val (x P) := by
  let u (P : T) : Multiplicative (ArchimedeanAdeles.Construction.FiniteAdeles K) :=
    Multiplicative.ofAdd (sourceKPFiniteAdditiveSingle K P.val.val (x P))
  have h := map_prod (finiteCharacter K).toMonoidHom u Finset.univ
  change finiteCharacter K ((∏ P : T, u P).toAdd) = ∏ P : T, finiteCharacter K (u P).toAdd at h
  rw [toAdd_prod] at h
  change finiteCharacter K (sourceKPExteriorUpperAdele K S₀ T x) =
    ∏ P : T, finiteCharacter K (sourceKPFiniteAdditiveSingle K P.val.val (x P)) at h
  rw [h]
  apply Finset.prod_congr rfl
  intro P _
  exact (localFiniteCharacter_single K P.val.val (x P)).symm

end
end ArtinMatthews
