module

public import ArtinMatthews.MarkedPhysicalEndpointArithmetic


set_option backward.privateInPublic true
@[expose] public section

/-! The literal PD03 endpoint vectors, their band damping, and the lift
`P=(Dbm,s), Q=(Dar,n)`. The support and quotient identities are consequences
of actual distinct labels and rough cofactors. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

theorem markedPhysicalBandRough_of_rough {J : Type*} (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime) {W : ℝ}
    (hbelow : ∀ j p, p ∈ P j → (p : ℝ) < W) {m : ℕ}
    (hm : ∀ p : ℕ, p.Prime → p ∣ m → W ≤ (p : ℝ)) :
    MarkedPhysicalBandRough P m := by
  intro j p hp hpm
  exact (not_le_of_gt (hbelow j p hp)) (hm p (hP j p hp) hpm)

/-- Both endpoint vectors in `det:endpoints` have this value; taking the
conjugate on the left supplies the original unconjugated alpha factor. -/
def markedPhysicalEndpointVector {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (α β : ℕ → ℂ) (z : ℤ × ℤ) : ℂ :=
  if MarkedPhysicalEndpointSupport P M z.1.natAbs then
    conj (α (z.1.natAbs / markedPhysicalSupportedProduct P z.1.natAbs)) * β z.2.natAbs
  else 0

def markedPhysicalLift (G m s : ℕ) : ℤ × ℤ := ((G * m : ℕ), s)

theorem markedPhysicalEndpointVector_lift {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    {m : ℕ} (hm : MarkedPhysicalBandRough P m) (s : ℕ) (α β : ℕ → ℂ) :
    markedPhysicalEndpointVector P M α β (markedPhysicalLift (markedPhysicalMarkingProduct a) m s) =
      conj (α m) * β s := by
  simp only [markedPhysicalEndpointVector, markedPhysicalLift, Int.natAbs_natCast,
    ite_eq_left (markedPhysicalEndpointSupport_mul hP hdis a ha hm),
    markedPhysical_quotient_mul hP hdis a ha hm]

/-- The source exponent is a real half of the excess number of band
divisors; it is not replaced by truncated natural subtraction. -/
def markedPhysicalEndpointDamping {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (q : ℝ) (z : ℤ × ℤ) : ℝ :=
  q ^ ((((∑ j, bandCount (P j) z.1.natAbs : ℕ) : ℝ) - Fintype.card J * M) / 2)

theorem markedPhysicalEndpointDamping_of_support {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (q : ℝ) (z : ℤ × ℤ)
    (hz : MarkedPhysicalEndpointSupport P M z.1.natAbs) :
    markedPhysicalEndpointDamping P M q z = 1 := by
  unfold markedPhysicalEndpointDamping
  simp [hz.1]

theorem markedPhysicalEndpointDamping_lift {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    {m : ℕ} (hm : MarkedPhysicalBandRough P m) (s : ℕ) (q : ℝ) :
    markedPhysicalEndpointDamping P M q (markedPhysicalLift (markedPhysicalMarkingProduct a) m s) = 1 := by
  apply markedPhysicalEndpointDamping_of_support
  simpa only [markedPhysicalLift, Int.natAbs_natCast] using
    markedPhysicalEndpointSupport_mul hP hdis a ha hm

/-- Exact four-coefficient identity of the original Cauchy-square summand.
All ordered labels remain present in the two endpoint arguments. -/
theorem markedPhysicalEndpoint_pairing_lift {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (b a : MarkedPhysicalMarking P M)
    (hb : MarkedPhysicalMarkingDistinct b) (ha : MarkedPhysicalMarkingDistinct a)
    {m r : ℕ} (hm : MarkedPhysicalBandRough P m) (hr : MarkedPhysicalBandRough P r)
    (s n : ℕ) (α β : ℕ → ℂ) :
    conj (markedPhysicalEndpointVector P M α β (markedPhysicalLift (markedPhysicalMarkingProduct b) m s)) *
      markedPhysicalEndpointVector P M α β (markedPhysicalLift (markedPhysicalMarkingProduct a) r n) =
      α m * conj (α r) * β n * conj (β s) := by
  rw [markedPhysicalEndpointVector_lift hP hdis b hb hm,
    markedPhysicalEndpointVector_lift hP hdis a ha hr]
  simp only [map_mul, starRingEnd_self_apply]
  ring

theorem markedPhysicalMarkingProduct_split {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime) (pads : ℕ)
    (a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) (pads+1)) :
    markedPhysicalMarkingProduct (markedPhysicalMarkingEquiv P hP (pads+1) a) =
      markedRawCopiedProduct ((markedRawActiveSplit pads) a).1 *
        markedRawLastProduct ((markedRawActiveSplit pads) a).2 :=
  markedRawFullProduct_split pads a

theorem markedPhysicalEndpointVector_split_lift {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (pads : ℕ)
    (a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) (pads+1))
    (ha : MarkedRawActiveDistinct a) {m : ℕ} (hm : MarkedPhysicalBandRough P m)
    (s : ℕ) (α β : ℕ → ℂ) :
    markedPhysicalEndpointVector P (pads+1) α β
      (markedPhysicalLift (markedRawCopiedProduct ((markedRawActiveSplit pads) a).1 *
        markedRawLastProduct ((markedRawActiveSplit pads) a).2) m s) = conj (α m) * β s := by
  rw [← markedPhysicalMarkingProduct_split P hP pads a]
  exact markedPhysicalEndpointVector_lift hP hdis _
    ((markedPhysicalMarkingEquiv_distinct P hP (pads+1) a).mpr ha) hm s α β

/-- The signed determinant is the literal source quantity, with no
coprimality, endpoint-support or analytic assumption needed. -/
theorem markedPhysicalLift_det (D b a m s r n : ℕ) :
    markedMinorIntegerDet (markedPhysicalLift (D*b) m s) (markedPhysicalLift (D*a) r n) =
      (D : ℤ) * ((b : ℤ) * m * n - (a : ℤ) * r * s) := by
  simp only [markedMinorIntegerDet, markedPhysicalLift, Nat.cast_mul]
  ring

theorem markedPhysicalLift_det_quotient {D : ℕ} (hD : 0 < D) (b a m s r n : ℕ) :
    markedMinorIntegerDet (markedPhysicalLift (D*b) m s) (markedPhysicalLift (D*a) r n) / (D : ℤ) =
      (b : ℤ) * m * n - (a : ℤ) * r * s := by
  rw [markedPhysicalLift_det]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hD.ne')

end ArtinMatthews
