module

public import ArtinMatthews.SourceKPLocalCompactProductLift
public import ArtinMatthews.SourceKPFiniteCoverSupportedWord
public import ArtinMatthews.SourceKPRetainedAverage
public import ArtinMatthews.SourceKPTraceJacquetFiniteFiber
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

/-! The reflected retained tuple uses the actual projective lift of
each finite cover word. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "mk" => sourceFiniteKP2ProjectiveMk K hζ
local notation "prod" => sourceKPFiniteCoverPlaceProduct K hζ
local notation "emb" => sourceKPAdeleLocalCover K hζ
local notation "base" => sourceKPAdelicLocalBase K hζ

private theorem noncommProd_eq_of_multiset_eq {G : Type*} [Monoid G]
    {a b : Multiset G} (h : a = b) (ha) (hb) : a.noncommProd ha = b.noncommProd hb := by
  subst b
  rfl

theorem sourceKPFiniteCoverPlaceProduct_base_one (U : Finset Pr)
    (w : SourceKPFiniteCoverLocalWords K hζ) (P : Pr) (hP : P ∉ U) :
    base P (1, M (prod U w)) = 1 := by
  rw [sourceKPAdelicLocalBase_finite_representative, sourceKPFiniteCoverPlaceProduct_at K hζ U w P,
    ite_eq_right hP]
  exact (ProjGenLinGroup.mk : GL (Fin 2) (P.adicCompletion K) →* _).map_one

theorem sourceKPFiniteCoverPlaceProduct_retainedLift (S : Finset Pr)
    (w : SourceKPFiniteCoverLocalWords K hζ) :
    M (prod S w) = (sourceKPLocalCompactProductLift K hζ S (fun P => mk P.val (w P.val))).2 := by
  let j : F →* SourceKPAdelicProjective K hζ := (1 : F →* _).prod M
  let f (P : Pr) : F := emb P (w P)
  have hc : (S : Set Pr).Pairwise (fun P Q => Commute (f P) (f Q)) :=
    fun P _ Q _ h => sourceKPAdeleLocalCover_commute K hζ P Q h.symm _ _
  have hmap : j (prod S w) = S.noncommProd (fun P => j (f P))
      (fun _ hP _ hQ h => (hc hP hQ h).map j) := Finset.map_noncommProd S f hc j
  have he : j (prod S w) = sourceKPLocalCompactProductLift K hζ S (fun P => mk P.val (w P.val)) := by
    rw [hmap, sourceKPLocalCompactProductLift_noncommProd]
    change (S.val.map (fun P => j (f P))).noncommProd _ =
      ((Finset.univ : Finset S).val.map (fun P => j (f P.val))).noncommProd _
    have hm : (S.val.map (fun P => j (f P))) =
        ((Finset.univ : Finset S).val.map (fun P => j (f P.val))) := by
      rw [Finset.univ_eq_attach, Finset.attach_val]
      exact (Multiset.attach_map_val' S.val (fun P => j (f P))).symm
    exact noncommProd_eq_of_multiset_eq hm _ _
  exact congrArg Prod.snd he

local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "L" => sourceFiniteKP2Lift K hζ
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "ev" => sourceKPAdeleMatrixAt K

def sourceKPReflectedC1RetainedWord (S₀ : Finset Pr) (m : Kˣ)
    (x : SWholeUnits K (sourceHilbertSet K S₀)) (R M₀ : sourceHilbertSet K S₀ → ℕ)
    (i : SourceKPRetainedSeedIndex K (sourceHilbertSet K S₀) R M₀) (a₀ : A) :
    SourceKPLocalCompactProductGroup K hζ (sourceHilbertSet K S₀) :=
  fun P => mk P.val
    (L P.val (sourceGL2Diagonal (σ P.val m)) * L P.val (sourceGL2Diagonal (x.2 P)) *
      (L P.val (sourceGL2Diagonal (-1)) * L P.val sourceGL2Weyl) *
      L P.val (sourceGL2Upper (sourceJacquetUpperRepresentative K P.val (R P) (M₀ P) (i P))) *
      L P.val (ev P.val a₀))

end
end ArtinMatthews
