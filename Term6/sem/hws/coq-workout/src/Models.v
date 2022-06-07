Require Import BinInt List Lia.

Import ListNotations.

From hahn Require Import HahnBase.

Require Export Id State Expr.

(* Thread identifier *)
Definition tid : Type := id. 

(* Locations (shared variables *)
Definition loc : Type := id. 

(* AST for statements *)
Inductive stmt : Type :=

| Assign : id -> expr -> stmt
| Read   : id -> loc -> stmt
| Write  : loc -> expr -> stmt
| Fence  : stmt

| Skip   : stmt
| Seq    : stmt -> stmt -> stmt
| If     : expr -> stmt -> stmt -> stmt
| While  : expr -> stmt -> stmt.

(* Program is a map from thread id to thread's code (ast) *)
Definition prog := state stmt.

(* Supplementary notation *)
Notation "r  '::=' e"                         := (Assign r e   ) (at level 37, no associativity).
Notation "r  '::=' '[' l ']'"                 := (Read r l     ) (at level 37, no associativity).
Notation "'[' l ']'  '::=' e"                 := (Write l e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Labels *)
Inductive label : Type := 
| R : loc -> Z -> label
| W : loc -> Z -> label
| F : label.

Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

(* Composition of states *)
Fixpoint compose {A : Type} (st st' : state A) := 
  match st' with 
  | nil             => st
  | cons (x, y) st' => compose (update st x y) st'
  end.

(* Thread-local state (map from registers to values) *)
Definition thrd_state := state Z.

Reserved Notation "c1 '--' l '-->' c2" (at level 0).

(* Thread-local step *)
Inductive thread_step : stmt * thrd_state -> option label -> stmt * thrd_state -> Prop := 

| ts_Assign (st : thrd_state) (r : id) (e : expr) (v : Z)
            (VAL : [| e |] st => v) :
    (r ::= e, st) -- None --> (Skip, (st [r <- v]))

| ts_Read (st : thrd_state) (r : id) (l : loc) (v : Z) :
    (r ::= [l], st) -- Some (R l v) --> (Skip, st [r <- v])

| ts_Write (st : thrd_state) (l : loc) (e : expr) (v : Z)
           (VAL : [| e |] st => v) :
    ([l] ::= e, st) -- Some (W l v) --> (Skip, st)

| ts_Fence (st : thrd_state) :
    (Fence, st) -- Some F --> (Skip, st)

| ts_Seq_Done (st : thrd_state) (s : stmt) :
    (Skip ;; s, st) -- None --> (s, st)

| ts_Seq_Step (st st' : thrd_state) (s1 s1' s2 : stmt) (olab : option label)
              (TSTEP : (s1, st) -- olab --> (s1', st')) :
    (s1 ;; s2, st) -- olab --> (s1' ;; s2, st')

| ts_If_True (st : thrd_state) (s1 s2 : stmt) (e : expr)
             (ETRUE : [| e |] st => Z.one) :
    (COND e THEN s1 ELSE s2 END, st) -- None --> (s1, st)

| ts_If_False (st : thrd_state) (s1 s2 : stmt) (e : expr)
              (EFALSE : [| e |] st => Z.zero) :
    (COND e THEN s1 ELSE s2 END, st) -- None --> (s2, st)

| ts_While (st : thrd_state) (s : stmt) (e : expr) :
    (WHILE e DO s END, st) -- None --> (COND e THEN s ;; WHILE e DO s END ELSE Skip END, st) 

  where "c1 -- l --> c2" := (thread_step c1 l c2).

(* State of the thread subsystem is two maps
 * 1) map from thread id to thread's code (ast)
 * 2) map from thread id to thread's state 
 *)
Definition thrdsys_state := (prog * state thrd_state)%type.

(* Initial states of threads *)
Definition init_state (p : prog) : state thrd_state := 
  map (fun '(i, _) => (i, nil)) p. 

Reserved Notation "c1 '==' l '==>' c2" (at level 0).

(* Step of the thread subsystem (i.e. step of one of program's threads) *)
Inductive thrdsys_step : thrdsys_state -> tid * option label -> thrdsys_state -> Prop := 
| Thrd_Step (prog : state stmt) (thrds_st : state thrd_state) 
            (s s' : stmt) (st st' : thrd_state) 
            (i : tid) (olab : option label)
            (TSTMT  : prog / i => s)
            (TSTATE : thrds_st / i => st)
            (TSTEP  : (s, st) -- olab --> (s', st')) :
    (prog, thrds_st) == (i, olab) ==> (prog [i <- s'], thrds_st [i <- st'])

  where "c1 == l ==> c2" := (thrdsys_step c1 l c2).

(* (Abstract) Memory Subsystem *)
Record memsys := make_memsys { 

  (* Type of the memory subsystem state *)
  mstate : Type;

  (* An initialization of the memory. 
   * Since we don't have alloc/dealloc instruction on our language, 
   * all shared memory should be explicitly preallocated. 
   * Thus we take a list of available locations (shared variables) as an additional argument.
   *)
  minit  : prog -> list loc -> mstate; 

  (* Step of the memory subsystem *)
  mstep  : mstate -> tid * option label -> mstate -> Prop;

}.

Reserved Notation "c1 '~~' l '~~>' c2" (at level 0).

(* Step of the whole system (thread subsystem + memory subsystem),
 * parametrized in the choice of the memory subsystem
 *)
Inductive step {Mem : memsys} : 
  thrdsys_state * Mem.(mstate) -> tid * option label -> thrdsys_state * Mem.(mstate) -> Prop := 

| Thrd_Eps_Step (st st' : thrdsys_state) (mst : Mem.(mstate)) (i : tid) 
                (TSTEP : st == (i, None) ==> st') : 
    (st, mst) ~~ (i, None) ~~> (st', mst)

| Mem_Eps_Step (st : thrdsys_state) (mst mst' : Mem.(mstate)) (i : tid) 
               (MSTEP : Mem.(mstep) mst (i, None) mst') : 
    (st, mst) ~~ (i, None) ~~> (st, mst')

| nEps_Step (st st' : thrdsys_state) (mst mst' : Mem.(mstate)) (i : tid) (lab : label)
            (TSTEP : st == (i, Some lab) ==> st')  
            (MSTEP : Mem.(mstep) mst (i, Some lab) mst') : 
    (st, mst) ~~ (i, Some lab) ~~> (st', mst')

  where "c1 ~~ l ~~> c2" := (step c1 l c2).

Reserved Notation "c1 '~~~>*' c2" (at level 0).

(* Reflexive-transitive closure of the system step *)
Inductive steps {Mem : memsys} : thrdsys_state * Mem.(mstate) -> thrdsys_state * Mem.(mstate) -> Prop := 
| Eps_Steps (st : thrdsys_state) (mst : Mem.(mstate)) : 
    (st, mst) ~~~>* (st, mst)

| Step_Steps (st st' st'' : thrdsys_state) (mst mst' mst'' : Mem.(mstate)) (i : tid) (olab : option label)
             (STEP  : (st , mst ) ~~ (i, olab) ~~> (st', mst')) 
             (STEPS : (st', mst') ~~~>* (st'', mst'')) : 
    (st , mst ) ~~~>* (st'', mst'')

  where "c1 ~~~>* c2" := (steps c1 c2).

(* Terminal program *)
Definition term_prog (p : prog) : prog := 
  map (fun '(i, _) => (i, Skip)) p.

(* An outcome of the program under given memory model. *)
Definition outcome (Mem : memsys) (p : prog) (locs : list loc) : state thrd_state -> Prop := 
  fun out => exists mout, ((p, init_state p), Mem.(minit) p locs) ~~~>* ((term_prog p, out), mout).

(* Sequentially Consistent Memory Model *)
Module SC. 
  
  Definition mstate := state Z.

  Definition minit (p : prog) (locs : list loc) : state Z := 
    map (fun l => (l, Z.zero)) locs.

  Inductive mstep : mstate -> tid * option label -> mstate -> Prop := 
  
  | Read_Step (l : loc) (v : Z) (i : tid) (st : mstate) 
              (VAL : st / l => v) : 
      mstep st (i , Some (R l v)) st

  | Write_Step (l : loc) (v : Z) (i : tid) (st : mstate) :
      mstep st (i , Some (W l v)) (st [l <- v])

  | Fence_Step (i : tid) (st : mstate) :
      mstep st (i , Some F) st.

End SC.

Definition sc_memsys := make_memsys SC.mstate SC.minit SC.mstep.

(* Total Store Order Memory Model *)
Module TSO. 

  Definition store_buf := list (id * Z).
  
  Record mstate := make_mstate {
    bufs : state store_buf;
    mem  : state Z;
  }.

  Definition minit (p : prog) (locs : list loc) : mstate := 
    let bufs := map (fun '(i, _) => (i, nil)) p in
    let mem  := map (fun l => (l, Z.zero)) locs in
    make_mstate bufs mem.

  (* Updates the memory state by flushing given buffer *)
  Definition flush (st : state Z) (buf : store_buf) : state Z := 
    compose st (rev buf).

  Inductive mstep : mstate -> tid * option label -> mstate -> Prop := 
  
  | Read_Step (l : loc) (v : Z) (i : tid) (st : mstate) (buf : store_buf)
              (TBUF : st.(bufs) / i => buf)
              (VAL : (flush st.(mem) buf) / l => v) : 
      mstep st (i, Some (R l v)) st

  | Write_Step (l : loc) (v : Z) (i : tid) (st : mstate) (buf : store_buf) 
               (TBUF : st.(bufs) / i => buf) :
      mstep st (i, Some (W l v)) (make_mstate (st.(bufs) [i <- (l, v) :: buf]) st.(mem))

  | Fence_Step (i : tid) (st : mstate) 
               (BEMP : st.(bufs) / i => []) :
      mstep st (i, Some F) st
  
  | Propagate_Step (l : loc) (v : Z) (i : tid) (st : mstate) (buf : store_buf) 
                   (nEMP : buf <> nil)
                   (TBUF : st.(bufs) / i => buf)
                   (LAST : (l, v) = last buf (0, Z.zero)) :
      mstep st (i, None) (make_mstate (st.(bufs) [i <- removelast buf]) (st.(mem) [l <- v])).

End TSO.

Definition tso_memsys := make_memsys TSO.mstate TSO.minit TSO.mstep.

(* Next comes the proof of the main theorem.
 * Lemma `tso_weaker_sc` states that every outcome of the program
 * under SC memory model is also an outcome of the program under TSO memory model.
 *)

(* The proof uses the (weak) simulation argument.
 * Given two small-step semantics (abstract machines) 
 * `p --> q` and `r ~~> s` suppose we want to show 
 * every outcome of the former semantics (`-->`) 
 * is also an outcome of the latter (`~~>`), 
 * i.e. that `~~>` machine can simulate `-->` machine.
 *
 * To do that, we need to `invent` a relation `R` (a sort of invariant) 
 * that will bind states of the abstract machines during the execution.
 *
 * Then we need to show that:
 *
 * 1) initial states of the machine are related by `R`, i.e. `R(p0, r0)` holds;
 *
 * 2) given `p`, `q`, and `r` such that  `p --> q` and `R(p, r)` holds, then
 *    there exists `s` such that `r ~~> s` and `R(q, s)` holds. 
 *    (in case of the weak simulation, `~~>` can make multiple steps, i.e. `r ~~>* s`);
 *
 * 3) finally, if `R(pn, rn)` holds and `pn` is a terminal state, 
 *    then `rn` is also a terminal state and 
 *     the `outcomes` of `pn` and `rn` coincides.
 * 
 * Given these three lemmas, proof that `~~>` simulates `-->` proceeds 
 * by an induction over the trace of the `-->` machine.
 *
 *)

(* This is a relation `R` for our simulaton proof, 
 * which binds states of the SC and TSO memory subsystems.
 * Your task is to invent the definition that would relate TSO machine to SC machine.  
 *)
Record simrel (p : prog) (msc : SC.mstate) (mtso : TSO.mstate) : Prop := make_simrel {

}.

(* Auxiliary lemma stating that the set of available threads
 * does not change during the evaluation 
 *)
Lemma thrdsys_step_eqv_tids (i : tid) l (st st' : thrdsys_state)
      (STEP : st == l ==> st') : 
  (exists s, (fst st) / i => s) <-> (exists s, (fst st') / i => s).
Proof. admit. Admitted.

(* Lemma stating that initial states of SC and TSO 
 * memory subsystems are bound by the relation `R`
 *)
Lemma siminit (p : prog) (locs : list loc) : 
  simrel p (SC.minit p locs) (TSO.minit p locs).
Proof. admit. Admitted.

(* Step of the weak simulation.
 * Evaluation step under SC memory subsystem 
 * can be simulated by several steps under TSO memory subsystem
 * and the relation `R` is preserved during the step.
 * 
 * Crucial part of the proof is to show that 
 * every non-epsilon step of the SC memory subsystem 
 * can be matched by several steps of the TSO memory subsystem.
 *
 *)
Lemma simstep (i : tid) (olab : option label)
      (st st' : thrdsys_state)
      (msc msc' : SC.mstate) (mtso : TSO.mstate)
      (SIMR : simrel (fst st) msc mtso)
      (STEP : @step sc_memsys (st, msc) (i, olab) (st', msc')) : 
  exists mtso', 
    (@steps tso_memsys (st, mtso) (st', mtso')) /\ 
    (simrel (fst st') msc' mtso').
Proof. admit. Admitted. 

(* A slightly more convinient for our proof induction principle *)
Lemma steps_indP {Mem : memsys} (st st' : thrdsys_state) (mst mst' : Mem.(mstate)) 
      (STEPS : (st, mst) ~~~>* (st', mst'))
      (P : thrdsys_state * Mem.(mstate) -> Prop)
      (PINIT : P (st, mst))
      (PSTEP : forall l st_ st_' mst_ mst_'
                      (PP : P (st_, mst_))
                      (STEP : (st_, mst_) ~~ l ~~> (st_', mst_')), 
          P (st_', mst_')
      ) : 
  P (st', mst').
Proof. 
  induction STEPS; auto.
  apply IHSTEPS.
  eapply PSTEP; eauto.
Qed.

(* Auxiliary predicate for the induction *)
Definition I (p : prog) (locs : list loc) : thrdsys_state * SC.mstate -> Prop := 
  fun '(st, msc) => exists mtso, 
      (@steps tso_memsys ((p, init_state p), TSO.minit p locs) (st, mtso)) /\       
      simrel (fst st) msc mtso.

(* Main theorem *)
Lemma tso_weaker_sc (p : prog) (locs : list loc) (out : state thrd_state) 
      (SC_out : outcome sc_memsys p locs out) :
  outcome tso_memsys p locs out.
Proof. 
  unfold outcome in *. 
  destruct SC_out as [msc SC_STEPS].
  edestruct @steps_indP 
    with (Mem := sc_memsys) (P := I p locs)
    as [mtso HH].
  { edone. }

  { exists (TSO.minit p locs). split.
    { constructor. }
    simpl. apply siminit. }

  { ins. desc. destruct l.
    edestruct simstep as [mtso' [STEPS SIMR]]; eauto. 
    exists mtso'; splits; auto.
    induction PP; auto.
    econstructor; eauto. }

  exists mtso. simpl in HH. by destruct HH as [HH _].

Qed.
