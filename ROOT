session "Framed_ODEs" = Ordinary_Differential_Equations +
  options [quick_and_dirty, document = pdf, document_output = "output"]
  sessions
    "Shallow_Expressions"
    "Hybrid-Library"
    Optics
    CAS_Integration
  theories
    Framed_ODEs
(*  document_files
    "root.tex" *)

session "Matrix_ODE_Verify" in Matrices = "Framed_ODEs" +
  options [quick_and_dirty, document = pdf, document_output = "output"]
  theories
    MTX_Preliminaries
    MTX_Norms
    SQ_MTX
    MTX_Flows

session "Hybrid-Verification" in "Hybrid_Programs" = "Matrix_ODE_Verify" +
  options [quick_and_dirty, document = pdf, document_output = "output"]
  theories
    Correctness_Specs
    Evolution_Commands
    Regular_Programs
    Diff_Dyn_Logic
    Proof_Automation
    HS_CAS_Integration
    Hybrid_Verification
(*  document_files
    "root.tex" *)

session "Verification_Examples" in "Hybrid_Programs/Verification_Examples" = "Hybrid-Verification" +
  options [quick_and_dirty, document = pdf, document_output = "output"]
  (*directories
    Hybrid_Programs/Verification_Examples
    Legacy*)
  theories
    "HS_Examples"
    "ARCH/ARCH"
    (*"Legacy/MTX_Examples"*)
  (* document_files
    "root.tex" *)

