module

public import ArtinMatthews.GiantSignedTraceAdmissibleWeight
public import ArtinMatthews.GiantSignedPackedChronology
public import ArtinMatthews.GiantSignedTraceChronologyReplay
public import ArtinMatthews.GiantSignedTraceDecodeReplay
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

/-! Admissible birth-distinct traces and packed chronologies retain the
same moves and the same ordered initial state. -/

namespace ArtinMatthews
noncomputable section

universe u

private theorem cast_evaluate {X Y : Type*} {T : X → Type*} (f : (x : X) → T x → Y)
    {a b : X} (h : a = b) (x : T a) :
    f b (cast (congrArg T h) x) = f a x := by
  subst b
  rfl

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}

abbrev GiantSignedPackedAdmissibleChronology
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) (ell : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ) :=
  {z : GiantSignedPackedChronology PS PB ell patterns C //
    GiantSignedChronologicalAdmissible κ z.2.2 ∧
      GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.2.2)}

variable (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i p, GiantTwoSidedPatternCoefficient PB (C i p) ell)

local notation "One" => fun _ _ _ _ => (1 : ℂ)
local notation "Rows" => giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K One
local notation "Traces" => GiantSignedAdmissibleBirthTrace (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K
local notation "Packed" => GiantSignedPackedChronology PS PB ell patterns C
local notation "Admissible" => GiantSignedPackedAdmissibleChronology PS PB ell patterns C κ

def giantSignedAdmissibleBirthTrace_pack (x : Traces) : Admissible :=
  let s : GiantSignedState PS PB (k+ell) := (x.1,x.2.1,giantSignedEmptyMemory PB)
  let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s x.2.2.val
  ⟨giantSignedTraceChronology_pack z,x.2.2.property⟩

private theorem replay_packed_heq {z z' : Packed} (he : z = z')
    (h : GiantSignedChronologicalCompatible κ z.2.2) (h' : GiantSignedChronologicalCompatible κ z'.2.2) :
    HEq (giantSignedTraceOfChronology ν V q ρ θ n patterns C κ visitQ ζ K z.1 z.2.1 z.2.2 h)
      (giantSignedTraceOfChronology ν V q ρ θ n patterns C κ visitQ ζ K z'.1 z'.2.1 z'.2.2 h') := by
  subst z'
  rfl

theorem giantSignedAdmissibleBirthTrace_pack_injective :
    Function.Injective (giantSignedAdmissibleBirthTrace_pack (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K) := by
  rintro ⟨y,a,t⟩ ⟨y',a',t'⟩ he
  let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
  let s' : GiantSignedState PS PB (k+ell) := (y',a',giantSignedEmptyMemory PB)
  let z := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s t.val
  let z' := giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s' t'.val
  have hp : giantSignedTraceChronology_pack z = giantSignedTraceChronology_pack z' :=
    congrArg Subtype.val he
  have h := replay_packed_heq ν V q ρ θ patterns C κ visitQ ζ K hp
    t.property.1.compatible t'.property.1.compatible
  have hr := giantSignedTraceChronology_replay ν V q ρ θ n patterns C κ visitQ ζ K s t.val t.property.1.compatible
  have hr' := giantSignedTraceChronology_replay ν V q ρ θ n patterns C κ visitQ ζ K s' t'.val t'.property.1.compatible
  have ht : HEq t.val t'.val := hr.symm.trans (h.trans hr')
  have hs : s = s' := z.first.symm.trans
    ((congrArg (fun u : Packed => u.2.2.state 0) hp).trans z'.first)
  have hy : y = y' := congrArg Prod.fst hs
  have ha : a = a' := congrArg (fun u : GiantSignedState PS PB (k+ell) => u.2.1) hs
  subst y'
  subst a'
  exact congrArg (fun w => (⟨y,a,w⟩ : Traces)) (Subtype.ext (eq_of_heq ht))

theorem giantSignedAdmissibleBirthTrace_pack_surjective :
    Function.Surjective (giantSignedAdmissibleBirthTrace_pack (PS := PS) ν V q ρ θ patterns C κ visitQ ζ K) := by
  rintro ⟨⟨p,batch,h⟩,ha,hd⟩
  let s : GiantSignedState PS PB (k+ell) := ((h.state 0).1,(h.state 0).2.1,giantSignedEmptyMemory PB)
  have hs : h.state 0 = s := Prod.ext rfl (Prod.ext rfl ha.boundary.1)
  let t₀ := giantSignedTraceOfChronology ν V q ρ θ n patterns C κ visitQ ζ K p batch h ha.compatible
  let t : GiantSignedTrace Rows s := cast (congrArg (GiantSignedTrace Rows) hs) t₀
  let decode (s' : GiantSignedState PS PB (k+ell)) (u : GiantSignedTrace Rows s') : Packed :=
    giantSignedTraceChronology_pack (giantSignedTraceChronology ν V q ρ θ n patterns C κ visitQ ζ K One s' u)
  have he : decode s t = ⟨p,batch,h⟩ := (cast_evaluate decode hs t₀).trans
    (giantSignedTraceOfChronology_decode ν V q ρ θ n patterns C κ visitQ ζ K p batch h ha.compatible)
  let Good (z : Packed) := GiantSignedChronologicalAdmissible κ z.2.2 ∧
    GiantSignedBirthDistinct (giantSignedChronologicalBirthData z.2.2)
  have hg : Good (decode s t) := he.symm ▸ (show Good ⟨p,batch,h⟩ from ⟨ha,hd⟩)
  refine ⟨⟨s.1,s.2.1,t,hg⟩,Subtype.ext ?_⟩
  exact he

def giantSignedAdmissibleBirthTraceEquiv : Traces ≃ Admissible :=
  Equiv.ofBijective (giantSignedAdmissibleBirthTrace_pack ν V q ρ θ patterns C κ visitQ ζ K)
    ⟨giantSignedAdmissibleBirthTrace_pack_injective ν V q ρ θ patterns C κ visitQ ζ K,
      giantSignedAdmissibleBirthTrace_pack_surjective ν V q ρ θ patterns C κ visitQ ζ K⟩

end
end ArtinMatthews
