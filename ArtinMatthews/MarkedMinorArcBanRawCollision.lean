module

public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedMinorArcBanCollision


set_option backward.privateInPublic true
@[expose] public section

/-! The actual prime-typed full-list ban and its symmetry on physical raw states. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators

def markedBanSnoc {X : Type*} {n : ℕ} (a : Fin n → X) (b : X) : Fin (n+1) → X :=
  Fin.snoc (α := fun _ => X) a b

theorem markedBanSnoc_castSucc {X : Type*} {n : ℕ} (a : Fin n → X) (b : X) (k : Fin n) :
    markedBanSnoc a b k.castSucc=a k := Fin.snoc_castSucc (α := fun _ => X) b a k

theorem markedBanSnoc_last {X : Type*} {n : ℕ} (a : Fin n → X) (b : X) :
    markedBanSnoc a b (Fin.last n)=b := Fin.snoc_last (α := fun _ => X) b a

def MarkedRawFullCrossBan {J : Type*} {P : J → Finset Nat.Primes} {M : ℕ}
    (source : MarkedRawActive P M) (fresh : (j : J) → ↥(P j)) : Prop :=
  ∃ i j k, (fresh i).1=(source j k).1

theorem markedRawFullCrossBan_snoc_iff {J : Type*} {P : J → Finset Nat.Primes} {pads : ℕ}
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (copied : MarkedRawActive P pads) (old fresh : (j : J) → ↥(P j))
    (hphysical : ∀ j, Function.Injective (markedBanSnoc (copied j) (fresh j))) :
    MarkedRawFullCrossBan (fun j => markedBanSnoc (copied j) (old j)) fresh ↔ ∃ j, old j=fresh j := by
  constructor
  · rintro ⟨i,j,k,he⟩
    have hij : i=j := by
      by_contra hn
      exact Finset.disjoint_left.mp (hd hn) (fresh i).2
        (he.symm ▸ (show ↥(P j) from markedBanSnoc (copied j) (old j) k).2)
    subst j
    change (fresh i).1=(markedBanSnoc (copied i) (old i) k : ↥(P i)).1 at he
    by_cases hk : k=Fin.last pads
    · subst k
      exact ⟨i,Subtype.ext (by simpa only [markedBanSnoc_last] using he.symm)⟩
    · have hkl : k.val < pads := by
        have hb := k.isLt
        have hn : k.val ≠ pads := fun h => hk (Fin.ext h)
        omega
      let k₀ : Fin pads := ⟨k.val,hkl⟩
      have hkc : k₀.castSucc=k := Fin.ext rfl
      rw [← hkc,markedBanSnoc_castSucc] at he
      have hs : markedBanSnoc (copied i) (fresh i) k₀.castSucc =
          markedBanSnoc (copied i) (fresh i) (Fin.last pads) := by
        simp only [markedBanSnoc_castSucc,markedBanSnoc_last]
        exact Subtype.ext he.symm
      have hv := congrArg Fin.val (hphysical i hs)
      have hb := k₀.isLt
      simp only [Fin.val_castSucc,Fin.val_last] at hv
      omega
  · rintro ⟨j,hj⟩
    refine ⟨j,j,Fin.last pads,?_⟩
    simp only [markedBanSnoc_last,hj]

theorem markedRawFullCrossBan_symmetric {J : Type*} {P : J → Finset Nat.Primes} {pads : ℕ}
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (copied : MarkedRawActive P pads) (old fresh : (j : J) → ↥(P j))
    (hold : ∀ j, Function.Injective (markedBanSnoc (copied j) (old j)))
    (hfresh : ∀ j, Function.Injective (markedBanSnoc (copied j) (fresh j))) :
    MarkedRawFullCrossBan (fun j => markedBanSnoc (copied j) (old j)) fresh ↔
      MarkedRawFullCrossBan (fun j => markedBanSnoc (copied j) (fresh j)) old := by
  rw [markedRawFullCrossBan_snoc_iff hd copied old fresh hfresh,
    markedRawFullCrossBan_snoc_iff hd copied fresh old hold]
  constructor <;> rintro ⟨j,hj⟩ <;> exact ⟨j,hj.symm⟩

def markedBanRawBandEquiv {J : Type*} (e : J → ℝ) (x : ℝ) (j : J) :
    ↥(markedRawActualPrimeBand e x j) ≃ ↥(markedLogPowerBand (e j) x) :=
  markedRawPrimeBandEquiv _ (fun _ hp => (mem_markedLogPowerBand.mp hp).1)

def markedBanRawLastEquiv {J : Type*} (e : J → ℝ) (x : ℝ) :
    ((j : J) → ↥(markedRawActualPrimeBand e x j)) ≃ MarkedFreshPrimeTuple e x :=
  Equiv.piCongrRight (markedBanRawBandEquiv e x)

def markedBanRawNaturalActive {J : Type*} (e : J → ℝ) (x : ℝ) {M : ℕ}
    (source : MarkedRawActive (markedRawActualPrimeBand e x) M) :
    (j : J) → Fin M → ↥(markedLogPowerBand (e j) x) :=
  fun j k => markedBanRawBandEquiv e x j (source j k)

theorem markedBanRawFullCrossBan_iff {J : Type*} (e : J → ℝ) (x : ℝ) {M : ℕ}
    (source : MarkedRawActive (markedRawActualPrimeBand e x) M)
    (fresh : (j : J) → ↥(markedRawActualPrimeBand e x j)) :
    MarkedRawFullCrossBan source fresh ↔
      MarkedBanFreshCollision (markedBanRawNaturalActive e x source) (markedBanRawLastEquiv e x fresh) := by
  constructor
  · rintro ⟨i,j,k,he⟩
    exact ⟨i,j,k,congrArg (fun p : Nat.Primes => (p:ℕ)) he⟩
  · rintro ⟨i,j,k,he⟩
    exact ⟨i,j,k,Subtype.ext he⟩

theorem markedBanRawLastMass_eq {J : Type*} [Fintype J] (e : J → ℝ) (q x : ℝ)
    (last : (j : J) → ↥(markedRawActualPrimeBand e x j)) :
    markedRawLastMass (markedRawActualPrimeAtom e q x) last =
      markedFreshTiltedLaw e q x (markedBanRawLastEquiv e x last) := by
  unfold markedRawLastMass markedFreshTiltedLaw finiteProductMass
  apply Finset.prod_congr rfl
  intro j _
  exact markedRawActualPrimeAtom_eq_tilted e q x j (last j)

theorem markedBanRawLastProduct_eq {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (last : (j : J) → ↥(markedRawActualPrimeBand e x j)) :
    (markedRawLastProduct last:ℤ)=markedFreshIntegerProduct e x (markedBanRawLastEquiv e x last) := rfl

theorem markedBan_actual_typed_disjoint_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, Pairwise (fun i j =>
      Disjoint (markedRawActualPrimeBand e x i) (markedRawActualPrimeBand e x j)) := by
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hd
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (hd hij)
    ((mem_markedRawPrimeBand _ p).mp hp) ((mem_markedRawPrimeBand _ p).mp hq)

end ArtinMatthews
