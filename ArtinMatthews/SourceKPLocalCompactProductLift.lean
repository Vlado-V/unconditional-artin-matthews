module

public import ArtinMatthews.SourceKPAdelicCompactSplit
public import ArtinMatthews.SourceKPLocalBorelEmbedding
public import ArtinMatthews.SourceKPLocalCompactGroup
public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceKPLocalCompactGlobalLevel
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

/-! Finite retained tuples act by the actual commuting local lifts in
the adelic cover. Their Borel and deep subgroups keep the same global
inclusions and phases. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "G" => SourceKPAdelicProjective K hζ
local notation "B" => sourceKPAdelicCoveringBorel K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ

abbrev SourceKPLocalCompactProductGroup :=
  (P : S) → SourceFiniteKP2Projective K hζ P.val

abbrev SourceKPLocalCompactProductBorel :=
  (P : S) → SourceFiniteKPProjectiveBorel K hζ P.val

abbrev SourceKPLocalCompactProductCompact :=
  (P : S) → sourceKPLocalCompactCover K hζ P.val

abbrev SourceKPLocalCompactProductDeep :=
  (P : S) → sourceKPLocalCompactDeep K hζ P.val

local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "Bₛ" => SourceKPLocalCompactProductBorel K hζ S
local notation "Cₛ" => SourceKPLocalCompactProductCompact K hζ S
local notation "Jₛ" => SourceKPLocalCompactProductDeep K hζ S

private theorem sourceKPLocalCompactProductLift_commute {P Q : S} (h : P ≠ Q)
    (x : SourceFiniteKP2Projective K hζ P.val) (y : SourceFiniteKP2Projective K hζ Q.val) :
    Commute (sourceKPAdelicLocalProjective K hζ P.val x)
      (sourceKPAdelicLocalProjective K hζ Q.val y) :=
  sourceKPAdelicLocalProjective_commute K hζ P.val Q.val
    (fun h' => h (Subtype.ext h'.symm)) x y

def sourceKPLocalCompactProductLift : Gₛ →* G :=
  MonoidHom.noncommPiCoprod (fun P : S => sourceKPAdelicLocalProjective K hζ P.val)
    (fun {P Q} h x y => sourceKPLocalCompactProductLift_commute K hζ S (P:=P) (Q:=Q) h x y)

local notation "L" => sourceKPLocalCompactProductLift K hζ S

private theorem sourceKPLocalCompactProductBorelLift_commute {P Q : S} (h : P ≠ Q)
    (x : SourceFiniteKPProjectiveBorel K hζ P.val) (y : SourceFiniteKPProjectiveBorel K hζ Q.val) :
    Commute (sourceKPAdelicLocalBorel K hζ P.val x)
      (sourceKPAdelicLocalBorel K hζ Q.val y) := by
  apply Subtype.ext
  exact (sourceKPLocalCompactProductLift_commute K hζ S h x.val y.val).eq

def sourceKPLocalCompactProductBorelLift : Bₛ →* B :=
  MonoidHom.noncommPiCoprod (fun P : S => sourceKPAdelicLocalBorel K hζ P.val)
    (fun {P Q} h x y => sourceKPLocalCompactProductBorelLift_commute K hζ S (P:=P) (Q:=Q) h x y)

local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ S

theorem sourceKPLocalCompactProductLift_noncommProd (g : Gₛ) :
    L g = (Finset.univ : Finset S).noncommProd
      (fun P => sourceKPAdelicLocalProjective K hζ P.val (g P))
      (fun _ _ _ _ h => sourceKPLocalCompactProductLift_commute K hζ S h _ _) := rfl

theorem sourceKPLocalCompactProductBorelLift_noncommProd (b : Bₛ) :
    Lᴮ b = (Finset.univ : Finset S).noncommProd
      (fun P => sourceKPAdelicLocalBorel K hζ P.val (b P))
      (fun _ _ _ _ h => sourceKPLocalCompactProductBorelLift_commute K hζ S h _ _) := rfl

theorem sourceKPLocalCompactProductBorelLift_val (b : Bₛ) :
    (Lᴮ b).val = L (fun P => (b P).val) := by
  change (B).subtype (Lᴮ b) = _
  rw [sourceKPLocalCompactProductBorelLift_noncommProd K hζ S b,
    sourceKPLocalCompactProductLift_noncommProd K hζ S]
  exact Finset.map_noncommProd _ _ _ (B).subtype

theorem sourceKPLocalCompactProductLift_commute_of_base_one (g : Gₛ) (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) : Commute (L g) r := by
  have hc (P : S) (x : SourceFiniteKP2Projective K hζ P.val) :
      Commute r (sourceKPAdelicLocalProjective K hζ P.val x) :=
    (sourceKPAdelicLocalProjective_commute_of_base_one K hζ P.val x r (hr P)).symm
  exact (MonoidHom.commute_noncommPiCoprod
    (fun P : S => sourceKPAdelicLocalProjective K hζ P.val)
    (hcomm := fun {P Q} h x y => sourceKPLocalCompactProductLift_commute K hζ S (P:=P) (Q:=Q) h x y)
    hc g).symm

theorem sourceKPLocalCompactProductDeep_mem (j : Jₛ) :
    L (fun P => (j P).val.val) ∈ D := by
  rw [sourceKPLocalCompactProductLift_noncommProd K hζ S]
  apply Subgroup.noncommProd_mem
  intro P _
  exact sourceKPLocalCompactDeepCoverLevel_global_mem K hζ P.val
    (show (j P).val.val ∈ sourceKPLocalCompactDeepCoverLevel K hζ P.val from
      ⟨(j P).val,(j P).property,rfl⟩)

theorem sourceKPLocalCompactProductCover_Iwasawa (g : Gₛ) :
    ∃ (b : Bₛ) (k : Cₛ), g = (fun P => (b P).val) * (fun P => (k P).val) := by
  choose b k h using fun P : S => sourceKPLocalCompactCover_Iwasawa K hζ P.val (g P)
  exact ⟨b,k,funext h⟩

end
end ArtinMatthews
