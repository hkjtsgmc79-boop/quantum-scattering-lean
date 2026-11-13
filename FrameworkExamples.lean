import QuantumScattering.FrameworkCompletion
noncomputable section
open QuantumScattering

-- Same global endpoint, arbitrary finite real layers and unequal open leads.
example (p : PhysicalProblem) : ReusableFrameworkCertificate p :=
  reusable_finite_layer_framework p

-- Inserting an artificial interface must preserve the full complex S, not just T.
example (l r : Port) (xs ys : Stack) (δ a b : ℝ) (ha:0<a) (hb:0<b) :
    (channelTransfer l r (Stack.transfer
      (xs++[Layer.segment δ (a+b) (add_pos ha hb)]++ys))).scatteringMatrix=
    (channelTransfer l r (Stack.transfer
      (xs++[Layer.segment δ a ha,Layer.segment δ b hb]++ys))).scatteringMatrix :=
  Stack.split_scattering l r xs ys δ a b ha hb

-- A different backend: smooth nonconstant interior, actual global ODE and uniqueness.
example (L : ℝ) (hL:0<L) (l r : Port) (iL iR : ℂ) :
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ),
      (SmoothBackend.segment L hL l r).Admissible iL iR fv.1 fv.2 :=
  SmoothBackend.smooth_scattering_unique L hL l r iL iR
