open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | DoNotUnfoldPureLets 
  | ReduceDivLets 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldFully of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Ident.lid Prims.list 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe 
  | NBE 
  | ForExtraction 
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____106 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____117 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____128 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____140 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____158 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____169 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____180 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____191 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____202 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____213 -> false
  
let (uu___is_ReduceDivLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReduceDivLets  -> true | uu____224 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____236 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____257 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____284 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____311 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____335 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____346 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____357 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____368 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____379 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____390 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____401 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____412 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____423 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____434 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____445 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____456 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____467 -> false
  
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1  ->
    fun s2  ->
      match (s1, s2) with
      | (Beta ,Beta ) -> true
      | (Iota ,Iota ) -> true
      | (Zeta ,Zeta ) -> true
      | (Weak ,Weak ) -> true
      | (HNF ,HNF ) -> true
      | (Primops ,Primops ) -> true
      | (Eager_unfolding ,Eager_unfolding ) -> true
      | (Inlining ,Inlining ) -> true
      | (DoNotUnfoldPureLets ,DoNotUnfoldPureLets ) -> true
      | (ReduceDivLets ,ReduceDivLets ) -> true
      | (UnfoldTac ,UnfoldTac ) -> true
      | (PureSubtermsWithinComputations ,PureSubtermsWithinComputations ) ->
          true
      | (Simplify ,Simplify ) -> true
      | (EraseUniverses ,EraseUniverses ) -> true
      | (AllowUnboundUniverses ,AllowUnboundUniverses ) -> true
      | (Reify ,Reify ) -> true
      | (CompressUvars ,CompressUvars ) -> true
      | (NoFullNorm ,NoFullNorm ) -> true
      | (CheckNoUvars ,CheckNoUvars ) -> true
      | (Unmeta ,Unmeta ) -> true
      | (Unascribe ,Unascribe ) -> true
      | (NBE ,NBE ) -> true
      | (Exclude s11,Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11,UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1,UnfoldOnly lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldFully lids1,UnfoldFully lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldAttr lids1,UnfoldAttr lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | uu____528 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____554 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____565 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____576 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____588 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
type name_prefix = Prims.string Prims.list
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
type mlift =
  {
  mlift_wp:
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
and edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
and effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list
    ;
  polymonadic_binds:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident *
      (env ->
         FStar_Syntax_Syntax.comp_typ ->
           FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
             FStar_Syntax_Syntax.comp_typ ->
               FStar_Syntax_Syntax.cflag Prims.list ->
                 FStar_Range.range ->
                   (FStar_Syntax_Syntax.comp *
                     FStar_TypeChecker_Common.guard_t)))
      Prims.list
    }
and env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: FStar_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
  gamma_cache: cached_elt FStar_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap ;
  attrtab: FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs:
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list
    ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq: Prims.bool ;
  use_eq_strict: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  phase1: Prims.bool ;
  failhard: Prims.bool ;
  nosynth: Prims.bool ;
  uvar_subtyping: Prims.bool ;
  tc_term:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t)
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t
    ;
  use_bv_sorts: Prims.bool ;
  qtbl_name_and_index:
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option)
    ;
  normalized_eff_names: FStar_Ident.lident FStar_Util.smap ;
  fv_delta_depths: FStar_Syntax_Syntax.delta_depth FStar_Util.smap ;
  proof_ns: proof_namespace ;
  synth_hook:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  try_solve_implicits_hook:
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit
    ;
  splice:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
  mpreprocess:
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  postprocess:
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  is_native_tactic: FStar_Ident.lid -> Prims.bool ;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_Syntax_DsEnv.env ;
  nbe:
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  strict_args_tab:
    Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap ;
  erasable_types_tab: Prims.bool FStar_Util.smap }
and solver_t =
  {
  init: env -> unit ;
  push: Prims.string -> unit ;
  pop: Prims.string -> unit ;
  snapshot: Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit) ;
  rollback:
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit
    ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list ;
  solve:
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit
    ;
  finish: unit -> unit ;
  refresh: unit -> unit }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    env ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_term
  
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mlift
  
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> decls
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> joins
  
let (__proj__Mkeffects__item__polymonadic_binds :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident *
      (env ->
         FStar_Syntax_Syntax.comp_typ ->
           FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
             FStar_Syntax_Syntax.comp_typ ->
               FStar_Syntax_Syntax.cflag Prims.list ->
                 FStar_Range.range ->
                   (FStar_Syntax_Syntax.comp *
                     FStar_TypeChecker_Common.guard_t)))
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls; order; joins; polymonadic_binds;_} -> polymonadic_binds
  
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_eq_strict
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> uvar_subtyping
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> try_solve_implicits_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> splice1
  
let (__proj__Mkenv__item__mpreprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> mpreprocess
  
let (__proj__Mkenv__item__postprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> dsenv
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> erasable_types_tab
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> init1
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> push1
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> pop1
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t -> Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> snapshot1
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> rollback1
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> encode_sig
  
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> finish1
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> refresh
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook;_} -> tc_push_in_gamma_hook
  
type lift_comp_t =
  env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
type polymonadic_bind_t =
  env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.comp_typ ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t)
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type implicit = FStar_TypeChecker_Common.implicit
type implicits = FStar_TypeChecker_Common.implicits
type guard_t = FStar_TypeChecker_Common.guard_t
let (preprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun tau  -> fun tm  -> env.mpreprocess env tau tm 
let (postprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  -> fun tau  -> fun ty  -> fun tm  -> env.postprocess env tau ty tm 
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___0_14348  ->
              match uu___0_14348 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14351 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____14351  in
                  let uu____14352 =
                    let uu____14353 = FStar_Syntax_Subst.compress y  in
                    uu____14353.FStar_Syntax_Syntax.n  in
                  (match uu____14352 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14357 =
                         let uu___327_14358 = y1  in
                         let uu____14359 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___327_14358.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___327_14358.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14359
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14357
                   | uu____14362 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___333_14376 = env  in
      let uu____14377 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___333_14376.solver);
        range = (uu___333_14376.range);
        curmodule = (uu___333_14376.curmodule);
        gamma = uu____14377;
        gamma_sig = (uu___333_14376.gamma_sig);
        gamma_cache = (uu___333_14376.gamma_cache);
        modules = (uu___333_14376.modules);
        expected_typ = (uu___333_14376.expected_typ);
        sigtab = (uu___333_14376.sigtab);
        attrtab = (uu___333_14376.attrtab);
        instantiate_imp = (uu___333_14376.instantiate_imp);
        effects = (uu___333_14376.effects);
        generalize = (uu___333_14376.generalize);
        letrecs = (uu___333_14376.letrecs);
        top_level = (uu___333_14376.top_level);
        check_uvars = (uu___333_14376.check_uvars);
        use_eq = (uu___333_14376.use_eq);
        use_eq_strict = (uu___333_14376.use_eq_strict);
        is_iface = (uu___333_14376.is_iface);
        admit = (uu___333_14376.admit);
        lax = (uu___333_14376.lax);
        lax_universes = (uu___333_14376.lax_universes);
        phase1 = (uu___333_14376.phase1);
        failhard = (uu___333_14376.failhard);
        nosynth = (uu___333_14376.nosynth);
        uvar_subtyping = (uu___333_14376.uvar_subtyping);
        tc_term = (uu___333_14376.tc_term);
        type_of = (uu___333_14376.type_of);
        universe_of = (uu___333_14376.universe_of);
        check_type_of = (uu___333_14376.check_type_of);
        use_bv_sorts = (uu___333_14376.use_bv_sorts);
        qtbl_name_and_index = (uu___333_14376.qtbl_name_and_index);
        normalized_eff_names = (uu___333_14376.normalized_eff_names);
        fv_delta_depths = (uu___333_14376.fv_delta_depths);
        proof_ns = (uu___333_14376.proof_ns);
        synth_hook = (uu___333_14376.synth_hook);
        try_solve_implicits_hook = (uu___333_14376.try_solve_implicits_hook);
        splice = (uu___333_14376.splice);
        mpreprocess = (uu___333_14376.mpreprocess);
        postprocess = (uu___333_14376.postprocess);
        is_native_tactic = (uu___333_14376.is_native_tactic);
        identifier_info = (uu___333_14376.identifier_info);
        tc_hooks = (uu___333_14376.tc_hooks);
        dsenv = (uu___333_14376.dsenv);
        nbe = (uu___333_14376.nbe);
        strict_args_tab = (uu___333_14376.strict_args_tab);
        erasable_types_tab = (uu___333_14376.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14385  -> fun uu____14386  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___340_14408 = env  in
      {
        solver = (uu___340_14408.solver);
        range = (uu___340_14408.range);
        curmodule = (uu___340_14408.curmodule);
        gamma = (uu___340_14408.gamma);
        gamma_sig = (uu___340_14408.gamma_sig);
        gamma_cache = (uu___340_14408.gamma_cache);
        modules = (uu___340_14408.modules);
        expected_typ = (uu___340_14408.expected_typ);
        sigtab = (uu___340_14408.sigtab);
        attrtab = (uu___340_14408.attrtab);
        instantiate_imp = (uu___340_14408.instantiate_imp);
        effects = (uu___340_14408.effects);
        generalize = (uu___340_14408.generalize);
        letrecs = (uu___340_14408.letrecs);
        top_level = (uu___340_14408.top_level);
        check_uvars = (uu___340_14408.check_uvars);
        use_eq = (uu___340_14408.use_eq);
        use_eq_strict = (uu___340_14408.use_eq_strict);
        is_iface = (uu___340_14408.is_iface);
        admit = (uu___340_14408.admit);
        lax = (uu___340_14408.lax);
        lax_universes = (uu___340_14408.lax_universes);
        phase1 = (uu___340_14408.phase1);
        failhard = (uu___340_14408.failhard);
        nosynth = (uu___340_14408.nosynth);
        uvar_subtyping = (uu___340_14408.uvar_subtyping);
        tc_term = (uu___340_14408.tc_term);
        type_of = (uu___340_14408.type_of);
        universe_of = (uu___340_14408.universe_of);
        check_type_of = (uu___340_14408.check_type_of);
        use_bv_sorts = (uu___340_14408.use_bv_sorts);
        qtbl_name_and_index = (uu___340_14408.qtbl_name_and_index);
        normalized_eff_names = (uu___340_14408.normalized_eff_names);
        fv_delta_depths = (uu___340_14408.fv_delta_depths);
        proof_ns = (uu___340_14408.proof_ns);
        synth_hook = (uu___340_14408.synth_hook);
        try_solve_implicits_hook = (uu___340_14408.try_solve_implicits_hook);
        splice = (uu___340_14408.splice);
        mpreprocess = (uu___340_14408.mpreprocess);
        postprocess = (uu___340_14408.postprocess);
        is_native_tactic = (uu___340_14408.is_native_tactic);
        identifier_info = (uu___340_14408.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14408.dsenv);
        nbe = (uu___340_14408.nbe);
        strict_args_tab = (uu___340_14408.strict_args_tab);
        erasable_types_tab = (uu___340_14408.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___344_14420 = e  in
      let uu____14421 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___344_14420.solver);
        range = (uu___344_14420.range);
        curmodule = (uu___344_14420.curmodule);
        gamma = (uu___344_14420.gamma);
        gamma_sig = (uu___344_14420.gamma_sig);
        gamma_cache = (uu___344_14420.gamma_cache);
        modules = (uu___344_14420.modules);
        expected_typ = (uu___344_14420.expected_typ);
        sigtab = (uu___344_14420.sigtab);
        attrtab = (uu___344_14420.attrtab);
        instantiate_imp = (uu___344_14420.instantiate_imp);
        effects = (uu___344_14420.effects);
        generalize = (uu___344_14420.generalize);
        letrecs = (uu___344_14420.letrecs);
        top_level = (uu___344_14420.top_level);
        check_uvars = (uu___344_14420.check_uvars);
        use_eq = (uu___344_14420.use_eq);
        use_eq_strict = (uu___344_14420.use_eq_strict);
        is_iface = (uu___344_14420.is_iface);
        admit = (uu___344_14420.admit);
        lax = (uu___344_14420.lax);
        lax_universes = (uu___344_14420.lax_universes);
        phase1 = (uu___344_14420.phase1);
        failhard = (uu___344_14420.failhard);
        nosynth = (uu___344_14420.nosynth);
        uvar_subtyping = (uu___344_14420.uvar_subtyping);
        tc_term = (uu___344_14420.tc_term);
        type_of = (uu___344_14420.type_of);
        universe_of = (uu___344_14420.universe_of);
        check_type_of = (uu___344_14420.check_type_of);
        use_bv_sorts = (uu___344_14420.use_bv_sorts);
        qtbl_name_and_index = (uu___344_14420.qtbl_name_and_index);
        normalized_eff_names = (uu___344_14420.normalized_eff_names);
        fv_delta_depths = (uu___344_14420.fv_delta_depths);
        proof_ns = (uu___344_14420.proof_ns);
        synth_hook = (uu___344_14420.synth_hook);
        try_solve_implicits_hook = (uu___344_14420.try_solve_implicits_hook);
        splice = (uu___344_14420.splice);
        mpreprocess = (uu___344_14420.mpreprocess);
        postprocess = (uu___344_14420.postprocess);
        is_native_tactic = (uu___344_14420.is_native_tactic);
        identifier_info = (uu___344_14420.identifier_info);
        tc_hooks = (uu___344_14420.tc_hooks);
        dsenv = uu____14421;
        nbe = (uu___344_14420.nbe);
        strict_args_tab = (uu___344_14420.strict_args_tab);
        erasable_types_tab = (uu___344_14420.erasable_types_tab)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14450) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14453,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14455,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14458 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____14472 . unit -> 'Auu____14472 FStar_Util.smap =
  fun uu____14479  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____14485 . unit -> 'Auu____14485 FStar_Util.smap =
  fun uu____14492  -> FStar_Util.smap_create (Prims.of_int (100)) 
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
           guard_t))
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
        ->
        (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
          (Prims.bool ->
             env ->
               FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
            ->
            solver_t ->
              FStar_Ident.lident ->
                (step Prims.list ->
                   env ->
                     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
                  -> env)
  =
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun check_type_of  ->
            fun solver  ->
              fun module_lid  ->
                fun nbe1  ->
                  let uu____14630 = new_gamma_cache ()  in
                  let uu____14633 = new_sigtab ()  in
                  let uu____14636 = new_sigtab ()  in
                  let uu____14643 =
                    let uu____14658 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14658, FStar_Pervasives_Native.None)  in
                  let uu____14679 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14683 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14687 = FStar_Options.using_facts_from ()  in
                  let uu____14688 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14691 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14692 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14706 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14630;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14633;
                    attrtab = uu____14636;
                    instantiate_imp = true;
                    effects =
                      {
                        decls = [];
                        order = [];
                        joins = [];
                        polymonadic_binds = []
                      };
                    generalize = true;
                    letrecs = [];
                    top_level = false;
                    check_uvars = false;
                    use_eq = false;
                    use_eq_strict = false;
                    is_iface = false;
                    admit = false;
                    lax = false;
                    lax_universes = false;
                    phase1 = false;
                    failhard = false;
                    nosynth = false;
                    uvar_subtyping = true;
                    tc_term;
                    type_of;
                    universe_of;
                    check_type_of;
                    use_bv_sorts = false;
                    qtbl_name_and_index = uu____14643;
                    normalized_eff_names = uu____14679;
                    fv_delta_depths = uu____14683;
                    proof_ns = uu____14687;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    try_solve_implicits_hook =
                      (fun e  ->
                         fun tau  ->
                           fun imps  -> failwith "no implicit hook available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    mpreprocess =
                      (fun e  ->
                         fun tau  ->
                           fun tm  -> failwith "no preprocessor available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____14821  -> false);
                    identifier_info = uu____14688;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14691;
                    nbe = nbe1;
                    strict_args_tab = uu____14692;
                    erasable_types_tab = uu____14706
                  }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env  -> env.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____14900  ->
    let uu____14901 = FStar_ST.op_Bang query_indices  in
    match uu____14901 with
    | [] -> failwith "Empty query indices!"
    | uu____14956 ->
        let uu____14966 =
          let uu____14976 =
            let uu____14984 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14984  in
          let uu____15038 = FStar_ST.op_Bang query_indices  in uu____14976 ::
            uu____15038
           in
        FStar_ST.op_Colon_Equals query_indices uu____14966
  
let (pop_query_indices : unit -> unit) =
  fun uu____15134  ->
    let uu____15135 = FStar_ST.op_Bang query_indices  in
    match uu____15135 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15262  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15299  ->
    match uu____15299 with
    | (l,n1) ->
        let uu____15309 = FStar_ST.op_Bang query_indices  in
        (match uu____15309 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____15431 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15454  ->
    let uu____15455 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15455
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____15523 =
       let uu____15526 = FStar_ST.op_Bang stack  in env :: uu____15526  in
     FStar_ST.op_Colon_Equals stack uu____15523);
    (let uu___418_15575 = env  in
     let uu____15576 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____15579 = FStar_Util.smap_copy (sigtab env)  in
     let uu____15582 = FStar_Util.smap_copy (attrtab env)  in
     let uu____15589 =
       let uu____15604 =
         let uu____15608 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15608  in
       let uu____15640 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15604, uu____15640)  in
     let uu____15689 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____15692 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____15695 =
       let uu____15698 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____15698  in
     let uu____15718 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____15731 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___418_15575.solver);
       range = (uu___418_15575.range);
       curmodule = (uu___418_15575.curmodule);
       gamma = (uu___418_15575.gamma);
       gamma_sig = (uu___418_15575.gamma_sig);
       gamma_cache = uu____15576;
       modules = (uu___418_15575.modules);
       expected_typ = (uu___418_15575.expected_typ);
       sigtab = uu____15579;
       attrtab = uu____15582;
       instantiate_imp = (uu___418_15575.instantiate_imp);
       effects = (uu___418_15575.effects);
       generalize = (uu___418_15575.generalize);
       letrecs = (uu___418_15575.letrecs);
       top_level = (uu___418_15575.top_level);
       check_uvars = (uu___418_15575.check_uvars);
       use_eq = (uu___418_15575.use_eq);
       use_eq_strict = (uu___418_15575.use_eq_strict);
       is_iface = (uu___418_15575.is_iface);
       admit = (uu___418_15575.admit);
       lax = (uu___418_15575.lax);
       lax_universes = (uu___418_15575.lax_universes);
       phase1 = (uu___418_15575.phase1);
       failhard = (uu___418_15575.failhard);
       nosynth = (uu___418_15575.nosynth);
       uvar_subtyping = (uu___418_15575.uvar_subtyping);
       tc_term = (uu___418_15575.tc_term);
       type_of = (uu___418_15575.type_of);
       universe_of = (uu___418_15575.universe_of);
       check_type_of = (uu___418_15575.check_type_of);
       use_bv_sorts = (uu___418_15575.use_bv_sorts);
       qtbl_name_and_index = uu____15589;
       normalized_eff_names = uu____15689;
       fv_delta_depths = uu____15692;
       proof_ns = (uu___418_15575.proof_ns);
       synth_hook = (uu___418_15575.synth_hook);
       try_solve_implicits_hook = (uu___418_15575.try_solve_implicits_hook);
       splice = (uu___418_15575.splice);
       mpreprocess = (uu___418_15575.mpreprocess);
       postprocess = (uu___418_15575.postprocess);
       is_native_tactic = (uu___418_15575.is_native_tactic);
       identifier_info = uu____15695;
       tc_hooks = (uu___418_15575.tc_hooks);
       dsenv = (uu___418_15575.dsenv);
       nbe = (uu___418_15575.nbe);
       strict_args_tab = uu____15718;
       erasable_types_tab = uu____15731
     })
  
let (pop_stack : unit -> env) =
  fun uu____15741  ->
    let uu____15742 = FStar_ST.op_Bang stack  in
    match uu____15742 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15796 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15886  ->
           let uu____15887 = snapshot_stack env  in
           match uu____15887 with
           | (stack_depth,env1) ->
               let uu____15921 = snapshot_query_indices ()  in
               (match uu____15921 with
                | (query_indices_depth,()) ->
                    let uu____15954 = (env1.solver).snapshot msg  in
                    (match uu____15954 with
                     | (solver_depth,()) ->
                         let uu____16011 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____16011 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___443_16078 = env1  in
                                 {
                                   solver = (uu___443_16078.solver);
                                   range = (uu___443_16078.range);
                                   curmodule = (uu___443_16078.curmodule);
                                   gamma = (uu___443_16078.gamma);
                                   gamma_sig = (uu___443_16078.gamma_sig);
                                   gamma_cache = (uu___443_16078.gamma_cache);
                                   modules = (uu___443_16078.modules);
                                   expected_typ =
                                     (uu___443_16078.expected_typ);
                                   sigtab = (uu___443_16078.sigtab);
                                   attrtab = (uu___443_16078.attrtab);
                                   instantiate_imp =
                                     (uu___443_16078.instantiate_imp);
                                   effects = (uu___443_16078.effects);
                                   generalize = (uu___443_16078.generalize);
                                   letrecs = (uu___443_16078.letrecs);
                                   top_level = (uu___443_16078.top_level);
                                   check_uvars = (uu___443_16078.check_uvars);
                                   use_eq = (uu___443_16078.use_eq);
                                   use_eq_strict =
                                     (uu___443_16078.use_eq_strict);
                                   is_iface = (uu___443_16078.is_iface);
                                   admit = (uu___443_16078.admit);
                                   lax = (uu___443_16078.lax);
                                   lax_universes =
                                     (uu___443_16078.lax_universes);
                                   phase1 = (uu___443_16078.phase1);
                                   failhard = (uu___443_16078.failhard);
                                   nosynth = (uu___443_16078.nosynth);
                                   uvar_subtyping =
                                     (uu___443_16078.uvar_subtyping);
                                   tc_term = (uu___443_16078.tc_term);
                                   type_of = (uu___443_16078.type_of);
                                   universe_of = (uu___443_16078.universe_of);
                                   check_type_of =
                                     (uu___443_16078.check_type_of);
                                   use_bv_sorts =
                                     (uu___443_16078.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___443_16078.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___443_16078.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___443_16078.fv_delta_depths);
                                   proof_ns = (uu___443_16078.proof_ns);
                                   synth_hook = (uu___443_16078.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___443_16078.try_solve_implicits_hook);
                                   splice = (uu___443_16078.splice);
                                   mpreprocess = (uu___443_16078.mpreprocess);
                                   postprocess = (uu___443_16078.postprocess);
                                   is_native_tactic =
                                     (uu___443_16078.is_native_tactic);
                                   identifier_info =
                                     (uu___443_16078.identifier_info);
                                   tc_hooks = (uu___443_16078.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___443_16078.nbe);
                                   strict_args_tab =
                                     (uu___443_16078.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___443_16078.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____16112  ->
             let uu____16113 =
               match depth with
               | FStar_Pervasives_Native.Some (s1,s2,s3,s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None  ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None)
                in
             match uu____16113 with
             | (stack_depth,query_indices_depth,solver_depth,dsenv_depth) ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth  in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth  in
                             ((let uu____16293 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16293
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____16309 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____16309
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____16341,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____16383 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16413  ->
                  match uu____16413 with
                  | (m,uu____16421) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16383 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___488_16436 = env  in
               {
                 solver = (uu___488_16436.solver);
                 range = (uu___488_16436.range);
                 curmodule = (uu___488_16436.curmodule);
                 gamma = (uu___488_16436.gamma);
                 gamma_sig = (uu___488_16436.gamma_sig);
                 gamma_cache = (uu___488_16436.gamma_cache);
                 modules = (uu___488_16436.modules);
                 expected_typ = (uu___488_16436.expected_typ);
                 sigtab = (uu___488_16436.sigtab);
                 attrtab = (uu___488_16436.attrtab);
                 instantiate_imp = (uu___488_16436.instantiate_imp);
                 effects = (uu___488_16436.effects);
                 generalize = (uu___488_16436.generalize);
                 letrecs = (uu___488_16436.letrecs);
                 top_level = (uu___488_16436.top_level);
                 check_uvars = (uu___488_16436.check_uvars);
                 use_eq = (uu___488_16436.use_eq);
                 use_eq_strict = (uu___488_16436.use_eq_strict);
                 is_iface = (uu___488_16436.is_iface);
                 admit = (uu___488_16436.admit);
                 lax = (uu___488_16436.lax);
                 lax_universes = (uu___488_16436.lax_universes);
                 phase1 = (uu___488_16436.phase1);
                 failhard = (uu___488_16436.failhard);
                 nosynth = (uu___488_16436.nosynth);
                 uvar_subtyping = (uu___488_16436.uvar_subtyping);
                 tc_term = (uu___488_16436.tc_term);
                 type_of = (uu___488_16436.type_of);
                 universe_of = (uu___488_16436.universe_of);
                 check_type_of = (uu___488_16436.check_type_of);
                 use_bv_sorts = (uu___488_16436.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_16436.normalized_eff_names);
                 fv_delta_depths = (uu___488_16436.fv_delta_depths);
                 proof_ns = (uu___488_16436.proof_ns);
                 synth_hook = (uu___488_16436.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_16436.try_solve_implicits_hook);
                 splice = (uu___488_16436.splice);
                 mpreprocess = (uu___488_16436.mpreprocess);
                 postprocess = (uu___488_16436.postprocess);
                 is_native_tactic = (uu___488_16436.is_native_tactic);
                 identifier_info = (uu___488_16436.identifier_info);
                 tc_hooks = (uu___488_16436.tc_hooks);
                 dsenv = (uu___488_16436.dsenv);
                 nbe = (uu___488_16436.nbe);
                 strict_args_tab = (uu___488_16436.strict_args_tab);
                 erasable_types_tab = (uu___488_16436.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16453,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___497_16469 = env  in
               {
                 solver = (uu___497_16469.solver);
                 range = (uu___497_16469.range);
                 curmodule = (uu___497_16469.curmodule);
                 gamma = (uu___497_16469.gamma);
                 gamma_sig = (uu___497_16469.gamma_sig);
                 gamma_cache = (uu___497_16469.gamma_cache);
                 modules = (uu___497_16469.modules);
                 expected_typ = (uu___497_16469.expected_typ);
                 sigtab = (uu___497_16469.sigtab);
                 attrtab = (uu___497_16469.attrtab);
                 instantiate_imp = (uu___497_16469.instantiate_imp);
                 effects = (uu___497_16469.effects);
                 generalize = (uu___497_16469.generalize);
                 letrecs = (uu___497_16469.letrecs);
                 top_level = (uu___497_16469.top_level);
                 check_uvars = (uu___497_16469.check_uvars);
                 use_eq = (uu___497_16469.use_eq);
                 use_eq_strict = (uu___497_16469.use_eq_strict);
                 is_iface = (uu___497_16469.is_iface);
                 admit = (uu___497_16469.admit);
                 lax = (uu___497_16469.lax);
                 lax_universes = (uu___497_16469.lax_universes);
                 phase1 = (uu___497_16469.phase1);
                 failhard = (uu___497_16469.failhard);
                 nosynth = (uu___497_16469.nosynth);
                 uvar_subtyping = (uu___497_16469.uvar_subtyping);
                 tc_term = (uu___497_16469.tc_term);
                 type_of = (uu___497_16469.type_of);
                 universe_of = (uu___497_16469.universe_of);
                 check_type_of = (uu___497_16469.check_type_of);
                 use_bv_sorts = (uu___497_16469.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___497_16469.normalized_eff_names);
                 fv_delta_depths = (uu___497_16469.fv_delta_depths);
                 proof_ns = (uu___497_16469.proof_ns);
                 synth_hook = (uu___497_16469.synth_hook);
                 try_solve_implicits_hook =
                   (uu___497_16469.try_solve_implicits_hook);
                 splice = (uu___497_16469.splice);
                 mpreprocess = (uu___497_16469.mpreprocess);
                 postprocess = (uu___497_16469.postprocess);
                 is_native_tactic = (uu___497_16469.is_native_tactic);
                 identifier_info = (uu___497_16469.identifier_info);
                 tc_hooks = (uu___497_16469.tc_hooks);
                 dsenv = (uu___497_16469.dsenv);
                 nbe = (uu___497_16469.nbe);
                 strict_args_tab = (uu___497_16469.strict_args_tab);
                 erasable_types_tab = (uu___497_16469.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___504_16512 = e  in
         {
           solver = (uu___504_16512.solver);
           range = r;
           curmodule = (uu___504_16512.curmodule);
           gamma = (uu___504_16512.gamma);
           gamma_sig = (uu___504_16512.gamma_sig);
           gamma_cache = (uu___504_16512.gamma_cache);
           modules = (uu___504_16512.modules);
           expected_typ = (uu___504_16512.expected_typ);
           sigtab = (uu___504_16512.sigtab);
           attrtab = (uu___504_16512.attrtab);
           instantiate_imp = (uu___504_16512.instantiate_imp);
           effects = (uu___504_16512.effects);
           generalize = (uu___504_16512.generalize);
           letrecs = (uu___504_16512.letrecs);
           top_level = (uu___504_16512.top_level);
           check_uvars = (uu___504_16512.check_uvars);
           use_eq = (uu___504_16512.use_eq);
           use_eq_strict = (uu___504_16512.use_eq_strict);
           is_iface = (uu___504_16512.is_iface);
           admit = (uu___504_16512.admit);
           lax = (uu___504_16512.lax);
           lax_universes = (uu___504_16512.lax_universes);
           phase1 = (uu___504_16512.phase1);
           failhard = (uu___504_16512.failhard);
           nosynth = (uu___504_16512.nosynth);
           uvar_subtyping = (uu___504_16512.uvar_subtyping);
           tc_term = (uu___504_16512.tc_term);
           type_of = (uu___504_16512.type_of);
           universe_of = (uu___504_16512.universe_of);
           check_type_of = (uu___504_16512.check_type_of);
           use_bv_sorts = (uu___504_16512.use_bv_sorts);
           qtbl_name_and_index = (uu___504_16512.qtbl_name_and_index);
           normalized_eff_names = (uu___504_16512.normalized_eff_names);
           fv_delta_depths = (uu___504_16512.fv_delta_depths);
           proof_ns = (uu___504_16512.proof_ns);
           synth_hook = (uu___504_16512.synth_hook);
           try_solve_implicits_hook =
             (uu___504_16512.try_solve_implicits_hook);
           splice = (uu___504_16512.splice);
           mpreprocess = (uu___504_16512.mpreprocess);
           postprocess = (uu___504_16512.postprocess);
           is_native_tactic = (uu___504_16512.is_native_tactic);
           identifier_info = (uu___504_16512.identifier_info);
           tc_hooks = (uu___504_16512.tc_hooks);
           dsenv = (uu___504_16512.dsenv);
           nbe = (uu___504_16512.nbe);
           strict_args_tab = (uu___504_16512.strict_args_tab);
           erasable_types_tab = (uu___504_16512.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____16532 =
        let uu____16533 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16533 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16532
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____16588 =
          let uu____16589 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16589 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16588
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____16644 =
          let uu____16645 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16645 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16644
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____16700 =
        let uu____16701 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16701 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16700
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___521_16765 = env  in
      {
        solver = (uu___521_16765.solver);
        range = (uu___521_16765.range);
        curmodule = lid;
        gamma = (uu___521_16765.gamma);
        gamma_sig = (uu___521_16765.gamma_sig);
        gamma_cache = (uu___521_16765.gamma_cache);
        modules = (uu___521_16765.modules);
        expected_typ = (uu___521_16765.expected_typ);
        sigtab = (uu___521_16765.sigtab);
        attrtab = (uu___521_16765.attrtab);
        instantiate_imp = (uu___521_16765.instantiate_imp);
        effects = (uu___521_16765.effects);
        generalize = (uu___521_16765.generalize);
        letrecs = (uu___521_16765.letrecs);
        top_level = (uu___521_16765.top_level);
        check_uvars = (uu___521_16765.check_uvars);
        use_eq = (uu___521_16765.use_eq);
        use_eq_strict = (uu___521_16765.use_eq_strict);
        is_iface = (uu___521_16765.is_iface);
        admit = (uu___521_16765.admit);
        lax = (uu___521_16765.lax);
        lax_universes = (uu___521_16765.lax_universes);
        phase1 = (uu___521_16765.phase1);
        failhard = (uu___521_16765.failhard);
        nosynth = (uu___521_16765.nosynth);
        uvar_subtyping = (uu___521_16765.uvar_subtyping);
        tc_term = (uu___521_16765.tc_term);
        type_of = (uu___521_16765.type_of);
        universe_of = (uu___521_16765.universe_of);
        check_type_of = (uu___521_16765.check_type_of);
        use_bv_sorts = (uu___521_16765.use_bv_sorts);
        qtbl_name_and_index = (uu___521_16765.qtbl_name_and_index);
        normalized_eff_names = (uu___521_16765.normalized_eff_names);
        fv_delta_depths = (uu___521_16765.fv_delta_depths);
        proof_ns = (uu___521_16765.proof_ns);
        synth_hook = (uu___521_16765.synth_hook);
        try_solve_implicits_hook = (uu___521_16765.try_solve_implicits_hook);
        splice = (uu___521_16765.splice);
        mpreprocess = (uu___521_16765.mpreprocess);
        postprocess = (uu___521_16765.postprocess);
        is_native_tactic = (uu___521_16765.is_native_tactic);
        identifier_info = (uu___521_16765.identifier_info);
        tc_hooks = (uu___521_16765.tc_hooks);
        dsenv = (uu___521_16765.dsenv);
        nbe = (uu___521_16765.nbe);
        strict_args_tab = (uu___521_16765.strict_args_tab);
        erasable_types_tab = (uu___521_16765.erasable_types_tab)
      }
  
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____16796 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16796
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16809 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16809)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16824 =
      let uu____16826 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16826  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16824)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16835  ->
    let uu____16836 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16836
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - Prims.int_one  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
  
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____16936) ->
          let vs = mk_univ_subst formals us  in
          let uu____16960 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16960)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16977  ->
    match uu___1_16977 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____17003  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____17023 = inst_tscheme t  in
      match uu____17023 with
      | (us,t1) ->
          let uu____17034 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____17034)
  
let (check_effect_is_not_a_template :
  FStar_Syntax_Syntax.eff_decl -> FStar_Range.range -> unit) =
  fun ed  ->
    fun rng  ->
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        let msg =
          let uu____17059 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____17061 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____17059 uu____17061
           in
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect, msg) rng
      else ()
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____17088  ->
          match uu____17088 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____17102 =
                    let uu____17104 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____17108 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____17112 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____17114 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____17104 uu____17108 uu____17112 uu____17114
                     in
                  failwith uu____17102)
               else ();
               (let uu____17119 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____17119))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____17137 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17148 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17159 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident]
              in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____17207) -> Maybe
             | (uu____17214,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____17234 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17328 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____17328 with
          | FStar_Pervasives_Native.None  ->
              let uu____17351 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_17395  ->
                     match uu___2_17395 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17434 = FStar_Ident.lid_equals lid l  in
                         if uu____17434
                         then
                           let uu____17457 =
                             let uu____17476 =
                               let uu____17491 = inst_tscheme t  in
                               FStar_Util.Inl uu____17491  in
                             let uu____17506 = FStar_Ident.range_of_lid l  in
                             (uu____17476, uu____17506)  in
                           FStar_Pervasives_Native.Some uu____17457
                         else FStar_Pervasives_Native.None
                     | uu____17559 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17351
                (fun uu____17597  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_17607  ->
                        match uu___3_17607 with
                        | (uu____17610,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17612);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17613;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17614;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17615;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17616;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17617;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17639 =
                                   let uu____17641 =
                                     FStar_Syntax_Util.lids_of_sigelt se  in
                                   FStar_All.pipe_right uu____17641
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17639
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids,s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____17694 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17701 -> cache t  in
                            let uu____17702 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17702 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17708 =
                                   let uu____17709 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17709)
                                    in
                                 maybe_cache uu____17708)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17780 = find_in_sigtab env lid  in
         match uu____17780 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17861 = lookup_qname env lid  in
      match uu____17861 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17882,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____17996 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____17996 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____18041 =
          let uu____18044 = lookup_attr env1 attr  in se1 :: uu____18044  in
        FStar_Util.smap_add (attrtab env1) attr uu____18041  in
      FStar_List.iter
        (fun attr  ->
           let uu____18054 =
             let uu____18055 = FStar_Syntax_Subst.compress attr  in
             uu____18055.FStar_Syntax_Syntax.n  in
           match uu____18054 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____18059 =
                 let uu____18061 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____18061.FStar_Ident.str  in
               add_one1 env se uu____18059
           | uu____18062 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____18085) ->
          add_sigelts env ses
      | uu____18094 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se)

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ * FStar_Range.range)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___4_18132  ->
           match uu___4_18132 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____18150 -> FStar_Pervasives_Native.None)
  
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
          FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____18212,lb::[]),uu____18214) ->
            let uu____18223 =
              let uu____18232 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18241 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18232, uu____18241)  in
            FStar_Pervasives_Native.Some uu____18223
        | FStar_Syntax_Syntax.Sig_let ((uu____18254,lbs),uu____18256) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18288 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18301 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18301
                     then
                       let uu____18314 =
                         let uu____18323 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18332 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18323, uu____18332)  in
                       FStar_Pervasives_Native.Some uu____18314
                     else FStar_Pervasives_Native.None)
        | uu____18355 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Range.range ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
          FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun rng  ->
        let inst_ts us_opt1 ts =
          match us_opt1 with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_new_effect ne ->
            (check_effect_is_not_a_template ne rng;
             (match us_opt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some us ->
                  if
                    (FStar_List.length us) <>
                      (FStar_List.length
                         (FStar_Pervasives_Native.fst
                            ne.FStar_Syntax_Syntax.signature))
                  then
                    let uu____18447 =
                      let uu____18449 =
                        let uu____18451 =
                          let uu____18453 =
                            let uu____18455 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18461 =
                              let uu____18463 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18463  in
                            Prims.op_Hat uu____18455 uu____18461  in
                          Prims.op_Hat ", expected " uu____18453  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18451
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18449
                       in
                    failwith uu____18447
                  else ());
             (let uu____18470 =
                let uu____18479 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18479, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18470))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18499,uu____18500) ->
            let uu____18505 =
              let uu____18514 =
                let uu____18519 =
                  let uu____18520 =
                    let uu____18523 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18523  in
                  (us, uu____18520)  in
                inst_ts us_opt uu____18519  in
              (uu____18514, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18505
        | uu____18542 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____18631 =
          match uu____18631 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18727,uvs,t,uu____18730,uu____18731,uu____18732);
                      FStar_Syntax_Syntax.sigrng = uu____18733;
                      FStar_Syntax_Syntax.sigquals = uu____18734;
                      FStar_Syntax_Syntax.sigmeta = uu____18735;
                      FStar_Syntax_Syntax.sigattrs = uu____18736;
                      FStar_Syntax_Syntax.sigopts = uu____18737;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18762 =
                     let uu____18771 = inst_tscheme1 (uvs, t)  in
                     (uu____18771, rng)  in
                   FStar_Pervasives_Native.Some uu____18762
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18795;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18797;
                      FStar_Syntax_Syntax.sigattrs = uu____18798;
                      FStar_Syntax_Syntax.sigopts = uu____18799;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18818 =
                     let uu____18820 = in_cur_mod env l  in uu____18820 = Yes
                      in
                   if uu____18818
                   then
                     let uu____18832 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18832
                      then
                        let uu____18848 =
                          let uu____18857 = inst_tscheme1 (uvs, t)  in
                          (uu____18857, rng)  in
                        FStar_Pervasives_Native.Some uu____18848
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18890 =
                        let uu____18899 = inst_tscheme1 (uvs, t)  in
                        (uu____18899, rng)  in
                      FStar_Pervasives_Native.Some uu____18890)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18924,uu____18925);
                      FStar_Syntax_Syntax.sigrng = uu____18926;
                      FStar_Syntax_Syntax.sigquals = uu____18927;
                      FStar_Syntax_Syntax.sigmeta = uu____18928;
                      FStar_Syntax_Syntax.sigattrs = uu____18929;
                      FStar_Syntax_Syntax.sigopts = uu____18930;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18973 =
                          let uu____18982 = inst_tscheme1 (uvs, k)  in
                          (uu____18982, rng)  in
                        FStar_Pervasives_Native.Some uu____18973
                    | uu____19003 ->
                        let uu____19004 =
                          let uu____19013 =
                            let uu____19018 =
                              let uu____19019 =
                                let uu____19022 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19022
                                 in
                              (uvs, uu____19019)  in
                            inst_tscheme1 uu____19018  in
                          (uu____19013, rng)  in
                        FStar_Pervasives_Native.Some uu____19004)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____19045,uu____19046);
                      FStar_Syntax_Syntax.sigrng = uu____19047;
                      FStar_Syntax_Syntax.sigquals = uu____19048;
                      FStar_Syntax_Syntax.sigmeta = uu____19049;
                      FStar_Syntax_Syntax.sigattrs = uu____19050;
                      FStar_Syntax_Syntax.sigopts = uu____19051;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19095 =
                          let uu____19104 = inst_tscheme_with (uvs, k) us  in
                          (uu____19104, rng)  in
                        FStar_Pervasives_Native.Some uu____19095
                    | uu____19125 ->
                        let uu____19126 =
                          let uu____19135 =
                            let uu____19140 =
                              let uu____19141 =
                                let uu____19144 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19144
                                 in
                              (uvs, uu____19141)  in
                            inst_tscheme_with uu____19140 us  in
                          (uu____19135, rng)  in
                        FStar_Pervasives_Native.Some uu____19126)
               | FStar_Util.Inr se ->
                   let uu____19180 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19201;
                          FStar_Syntax_Syntax.sigrng = uu____19202;
                          FStar_Syntax_Syntax.sigquals = uu____19203;
                          FStar_Syntax_Syntax.sigmeta = uu____19204;
                          FStar_Syntax_Syntax.sigattrs = uu____19205;
                          FStar_Syntax_Syntax.sigopts = uu____19206;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19223 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____19180
                     (FStar_Util.map_option
                        (fun uu____19271  ->
                           match uu____19271 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19302 =
          let uu____19313 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____19313 mapper  in
        match uu____19302 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19387 =
              let uu____19398 =
                let uu____19405 =
                  let uu___858_19408 = t  in
                  let uu____19409 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___858_19408.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19409;
                    FStar_Syntax_Syntax.vars =
                      (uu___858_19408.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19405)  in
              (uu____19398, r)  in
            FStar_Pervasives_Native.Some uu____19387
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19458 = lookup_qname env l  in
      match uu____19458 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19479 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19533 = try_lookup_bv env bv  in
      match uu____19533 with
      | FStar_Pervasives_Native.None  ->
          let uu____19548 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19548 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19564 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19565 =
            let uu____19566 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19566  in
          (uu____19564, uu____19565)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19588 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19588 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19654 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19654  in
          let uu____19655 =
            let uu____19664 =
              let uu____19669 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____19669)  in
            (uu____19664, r1)  in
          FStar_Pervasives_Native.Some uu____19655
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____19704 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19704 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19737,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19762 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19762  in
            let uu____19763 =
              let uu____19768 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19768, r1)  in
            FStar_Pervasives_Native.Some uu____19763
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19792 = try_lookup_lid env l  in
      match uu____19792 with
      | FStar_Pervasives_Native.None  ->
          let uu____19819 = name_not_found l  in
          let uu____19825 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19819 uu____19825
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19868  ->
              match uu___5_19868 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19872 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19893 = lookup_qname env lid  in
      match uu____19893 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19902,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19905;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19907;
              FStar_Syntax_Syntax.sigattrs = uu____19908;
              FStar_Syntax_Syntax.sigopts = uu____19909;_},FStar_Pervasives_Native.None
            ),uu____19910)
          ->
          let uu____19961 =
            let uu____19968 =
              let uu____19969 =
                let uu____19972 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19972 t  in
              (uvs, uu____19969)  in
            (uu____19968, q)  in
          FStar_Pervasives_Native.Some uu____19961
      | uu____19985 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20007 = lookup_qname env lid  in
      match uu____20007 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20012,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____20015;
              FStar_Syntax_Syntax.sigquals = uu____20016;
              FStar_Syntax_Syntax.sigmeta = uu____20017;
              FStar_Syntax_Syntax.sigattrs = uu____20018;
              FStar_Syntax_Syntax.sigopts = uu____20019;_},FStar_Pervasives_Native.None
            ),uu____20020)
          ->
          let uu____20071 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20071 (uvs, t)
      | uu____20076 ->
          let uu____20077 = name_not_found lid  in
          let uu____20083 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20077 uu____20083
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____20103 = lookup_qname env lid  in
      match uu____20103 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20108,uvs,t,uu____20111,uu____20112,uu____20113);
              FStar_Syntax_Syntax.sigrng = uu____20114;
              FStar_Syntax_Syntax.sigquals = uu____20115;
              FStar_Syntax_Syntax.sigmeta = uu____20116;
              FStar_Syntax_Syntax.sigattrs = uu____20117;
              FStar_Syntax_Syntax.sigopts = uu____20118;_},FStar_Pervasives_Native.None
            ),uu____20119)
          ->
          let uu____20176 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20176 (uvs, t)
      | uu____20181 ->
          let uu____20182 = name_not_found lid  in
          let uu____20188 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20182 uu____20188
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____20211 = lookup_qname env lid  in
      match uu____20211 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20219,uu____20220,uu____20221,uu____20222,uu____20223,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20225;
              FStar_Syntax_Syntax.sigquals = uu____20226;
              FStar_Syntax_Syntax.sigmeta = uu____20227;
              FStar_Syntax_Syntax.sigattrs = uu____20228;
              FStar_Syntax_Syntax.sigopts = uu____20229;_},uu____20230),uu____20231)
          -> (true, dcs)
      | uu____20296 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____20312 = lookup_qname env lid  in
      match uu____20312 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20313,uu____20314,uu____20315,l,uu____20317,uu____20318);
              FStar_Syntax_Syntax.sigrng = uu____20319;
              FStar_Syntax_Syntax.sigquals = uu____20320;
              FStar_Syntax_Syntax.sigmeta = uu____20321;
              FStar_Syntax_Syntax.sigattrs = uu____20322;
              FStar_Syntax_Syntax.sigopts = uu____20323;_},uu____20324),uu____20325)
          -> l
      | uu____20384 ->
          let uu____20385 =
            let uu____20387 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20387  in
          failwith uu____20385
  
let (lookup_definition_qninfo_aux :
  Prims.bool ->
    delta_level Prims.list ->
      FStar_Ident.lident ->
        qninfo ->
          (FStar_Syntax_Syntax.univ_name Prims.list *
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.option)
  =
  fun rec_ok  ->
    fun delta_levels  ->
      fun lid  ->
        fun qninfo  ->
          let visible quals =
            FStar_All.pipe_right delta_levels
              (FStar_Util.for_some
                 (fun dl  ->
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some (visible_at dl))))
             in
          match qninfo with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20457)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20514) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20538 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20538
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20573 -> FStar_Pervasives_Native.None)
          | uu____20582 -> FStar_Pervasives_Native.None
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo  ->
        lookup_definition_qninfo_aux true delta_levels lid qninfo
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____20644 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20644
  
let (lookup_nonrec_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____20677 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20677
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20729,uu____20730) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20779),uu____20780) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20829 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20847 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20857 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20874 ->
                  let uu____20881 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20881
              | FStar_Syntax_Syntax.Sig_let ((uu____20882,lbs),uu____20884)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20900 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20900
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20907 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20923 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20933 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20934 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20941 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20942 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20943 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20956 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20957 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20985 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20985
           (fun d_opt  ->
              let uu____20998 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20998
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____21008 =
                   let uu____21011 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____21011  in
                 match uu____21008 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____21012 =
                       let uu____21014 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____21014
                        in
                     failwith uu____21012
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____21019 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____21019
                       then
                         let uu____21022 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____21024 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____21026 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____21022 uu____21024 uu____21026
                       else ());
                      FStar_Util.smap_add env.fv_delta_depths
                        lid.FStar_Ident.str d;
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21051),uu____21052) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21101 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21123),uu____21124) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21173 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____21195 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21195
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21228 = lookup_attrs_of_lid env fv_lid1  in
        match uu____21228 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21250 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21259 =
                        let uu____21260 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21260.FStar_Syntax_Syntax.n  in
                      match uu____21259 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21265 -> false))
               in
            (true, uu____21250)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____21288 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____21288
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let cache_in_fv_tab :
  'a .
    'a FStar_Util.smap ->
      FStar_Syntax_Syntax.fv -> (unit -> (Prims.bool * 'a)) -> 'a
  =
  fun tab  ->
    fun fv  ->
      fun f  ->
        let s =
          let uu____21360 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____21360.FStar_Ident.str  in
        let uu____21361 = FStar_Util.smap_try_find tab s  in
        match uu____21361 with
        | FStar_Pervasives_Native.None  ->
            let uu____21364 = f ()  in
            (match uu____21364 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21402 =
        let uu____21403 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21403 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21437 =
        let uu____21438 = FStar_Syntax_Util.unrefine t  in
        uu____21438.FStar_Syntax_Syntax.n  in
      match uu____21437 with
      | FStar_Syntax_Syntax.Tm_type uu____21442 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21446) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21472) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21477,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21499 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21532 =
        let attrs =
          let uu____21538 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21538  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21578 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21578)
               in
            (true, res)
         in
      cache_in_fv_tab env.strict_args_tab fv f
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____21623 = lookup_qname env ftv  in
      match uu____21623 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21627) ->
          let uu____21672 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____21672 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21693,t),r) ->
               let uu____21708 =
                 let uu____21709 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21709 t  in
               FStar_Pervasives_Native.Some uu____21708)
      | uu____21710 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____21722 = try_lookup_effect_lid env ftv  in
      match uu____21722 with
      | FStar_Pervasives_Native.None  ->
          let uu____21725 = name_not_found ftv  in
          let uu____21731 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21725 uu____21731
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____21755 = lookup_qname env lid0  in
        match uu____21755 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21766);
                FStar_Syntax_Syntax.sigrng = uu____21767;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21769;
                FStar_Syntax_Syntax.sigattrs = uu____21770;
                FStar_Syntax_Syntax.sigopts = uu____21771;_},FStar_Pervasives_Native.None
              ),uu____21772)
            ->
            let lid1 =
              let uu____21828 =
                let uu____21829 = FStar_Ident.range_of_lid lid  in
                let uu____21830 =
                  let uu____21831 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21831  in
                FStar_Range.set_use_range uu____21829 uu____21830  in
              FStar_Ident.set_lid_range lid uu____21828  in
            let uu____21832 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21838  ->
                      match uu___6_21838 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21841 -> false))
               in
            if uu____21832
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21860 =
                      let uu____21862 =
                        let uu____21864 = get_range env  in
                        FStar_Range.string_of_range uu____21864  in
                      let uu____21865 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21867 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21862 uu____21865 uu____21867
                       in
                    failwith uu____21860)
                  in
               match (binders, univs1) with
               | ([],uu____21888) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21914,uu____21915::uu____21916::uu____21917) ->
                   let uu____21938 =
                     let uu____21940 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21942 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21940 uu____21942
                      in
                   failwith uu____21938
               | uu____21953 ->
                   let uu____21968 =
                     let uu____21973 =
                       let uu____21974 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21974)  in
                     inst_tscheme_with uu____21973 insts  in
                   (match uu____21968 with
                    | (uu____21987,t) ->
                        let t1 =
                          let uu____21990 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21990 t  in
                        let uu____21991 =
                          let uu____21992 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21992.FStar_Syntax_Syntax.n  in
                        (match uu____21991 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____22027 -> failwith "Impossible")))
        | uu____22035 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____22059 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____22059 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____22072,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22079 = find1 l2  in
            (match uu____22079 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22086 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____22086 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22090 = find1 l  in
            (match uu____22090 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____22095 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22095
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22116 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____22116 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22122) ->
            FStar_List.length bs
        | uu____22161 ->
            let uu____22162 =
              let uu____22168 =
                let uu____22170 = FStar_Ident.string_of_lid name  in
                let uu____22172 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22170 uu____22172
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22168)
               in
            FStar_Errors.raise_error uu____22162 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____22191 = lookup_qname env l1  in
      match uu____22191 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22194;
              FStar_Syntax_Syntax.sigrng = uu____22195;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22197;
              FStar_Syntax_Syntax.sigattrs = uu____22198;
              FStar_Syntax_Syntax.sigopts = uu____22199;_},uu____22200),uu____22201)
          -> q
      | uu____22254 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____22278 =
          let uu____22279 =
            let uu____22281 = FStar_Util.string_of_int i  in
            let uu____22283 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22281 uu____22283
             in
          failwith uu____22279  in
        let uu____22286 = lookup_datacon env lid  in
        match uu____22286 with
        | (uu____22291,t) ->
            let uu____22293 =
              let uu____22294 = FStar_Syntax_Subst.compress t  in
              uu____22294.FStar_Syntax_Syntax.n  in
            (match uu____22293 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22298) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____22342 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____22342
                      FStar_Pervasives_Native.fst)
             | uu____22353 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22367 = lookup_qname env l  in
      match uu____22367 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22369,uu____22370,uu____22371);
              FStar_Syntax_Syntax.sigrng = uu____22372;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22374;
              FStar_Syntax_Syntax.sigattrs = uu____22375;
              FStar_Syntax_Syntax.sigopts = uu____22376;_},uu____22377),uu____22378)
          ->
          FStar_Util.for_some
            (fun uu___7_22433  ->
               match uu___7_22433 with
               | FStar_Syntax_Syntax.Projector uu____22435 -> true
               | uu____22441 -> false) quals
      | uu____22443 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22457 = lookup_qname env lid  in
      match uu____22457 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22459,uu____22460,uu____22461,uu____22462,uu____22463,uu____22464);
              FStar_Syntax_Syntax.sigrng = uu____22465;
              FStar_Syntax_Syntax.sigquals = uu____22466;
              FStar_Syntax_Syntax.sigmeta = uu____22467;
              FStar_Syntax_Syntax.sigattrs = uu____22468;
              FStar_Syntax_Syntax.sigopts = uu____22469;_},uu____22470),uu____22471)
          -> true
      | uu____22531 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22545 = lookup_qname env lid  in
      match uu____22545 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22547,uu____22548,uu____22549,uu____22550,uu____22551,uu____22552);
              FStar_Syntax_Syntax.sigrng = uu____22553;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22555;
              FStar_Syntax_Syntax.sigattrs = uu____22556;
              FStar_Syntax_Syntax.sigopts = uu____22557;_},uu____22558),uu____22559)
          ->
          FStar_Util.for_some
            (fun uu___8_22622  ->
               match uu___8_22622 with
               | FStar_Syntax_Syntax.RecordType uu____22624 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22634 -> true
               | uu____22644 -> false) quals
      | uu____22646 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22656,uu____22657);
            FStar_Syntax_Syntax.sigrng = uu____22658;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22660;
            FStar_Syntax_Syntax.sigattrs = uu____22661;
            FStar_Syntax_Syntax.sigopts = uu____22662;_},uu____22663),uu____22664)
        ->
        FStar_Util.for_some
          (fun uu___9_22723  ->
             match uu___9_22723 with
             | FStar_Syntax_Syntax.Action uu____22725 -> true
             | uu____22727 -> false) quals
    | uu____22729 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22743 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22743
  
let (is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation]  in
  fun env  ->
    fun head1  ->
      let uu____22760 =
        let uu____22761 = FStar_Syntax_Util.un_uinst head1  in
        uu____22761.FStar_Syntax_Syntax.n  in
      match uu____22760 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22767 ->
               true
           | uu____22770 -> false)
      | uu____22772 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22786 = lookup_qname env l  in
      match uu____22786 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22789),uu____22790) ->
          FStar_Util.for_some
            (fun uu___10_22838  ->
               match uu___10_22838 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22841 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22843 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22919 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22937) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22955 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22963 ->
                 FStar_Pervasives_Native.Some true
             | uu____22982 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22985 =
        let uu____22989 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22989 mapper  in
      match uu____22985 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____23049 = lookup_qname env lid  in
      match uu____23049 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____23053,uu____23054,tps,uu____23056,uu____23057,uu____23058);
              FStar_Syntax_Syntax.sigrng = uu____23059;
              FStar_Syntax_Syntax.sigquals = uu____23060;
              FStar_Syntax_Syntax.sigmeta = uu____23061;
              FStar_Syntax_Syntax.sigattrs = uu____23062;
              FStar_Syntax_Syntax.sigopts = uu____23063;_},uu____23064),uu____23065)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23133 -> FStar_Pervasives_Native.None
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____23179  ->
              match uu____23179 with
              | (d,uu____23188) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____23204 = effect_decl_opt env l  in
      match uu____23204 with
      | FStar_Pervasives_Native.None  ->
          let uu____23219 = name_not_found l  in
          let uu____23225 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23219 uu____23225
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____23253 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____23253 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23260  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23274  ->
            fun uu____23275  -> fun e  -> FStar_Util.return_all e))
  } 
let (join_opt :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * mlift * mlift) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23309 = FStar_Ident.lid_equals l1 l2  in
        if uu____23309
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23328 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23328
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23347 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23400  ->
                        match uu____23400 with
                        | (m1,m2,uu____23414,uu____23415,uu____23416) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23347 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23441,uu____23442,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23490 = join_opt env l1 l2  in
        match uu____23490 with
        | FStar_Pervasives_Native.None  ->
            let uu____23511 =
              let uu____23517 =
                let uu____23519 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23521 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23519 uu____23521
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23517)  in
            FStar_Errors.raise_error uu____23511 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23564 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23564
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  'Auu____23584 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23584) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23613 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23639  ->
                match uu____23639 with
                | (d,uu____23646) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23613 with
      | FStar_Pervasives_Native.None  ->
          let uu____23657 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23657
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23672 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23672 with
           | (uu____23683,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23701)::(wp,uu____23703)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23759 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____23824 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23837 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23837 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23854 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23854 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23879 =
                     let uu____23885 =
                       let uu____23887 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23895 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23906 =
                         let uu____23908 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23908  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23887 uu____23895 uu____23906
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23885)
                      in
                   FStar_Errors.raise_error uu____23879
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23916 =
                     let uu____23927 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23927 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23964  ->
                        fun uu____23965  ->
                          match (uu____23964, uu____23965) with
                          | ((x,uu____23995),(t,uu____23997)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23916
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____24028 =
                     let uu___1614_24029 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1614_24029.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1614_24029.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1614_24029.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1614_24029.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____24028
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____24041 .
    'Auu____24041 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_res  ->
          let check_partial_application eff_name args =
            let r = get_range env  in
            let uu____24082 =
              let uu____24089 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____24089)  in
            match uu____24082 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24113 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24115 = FStar_Util.string_of_int given  in
                     let uu____24117 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24113 uu____24115 uu____24117
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24122 = effect_decl_opt env effect_name  in
          match uu____24122 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24144) ->
              let uu____24155 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24155 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24173 =
                       let uu____24176 = get_range env  in
                       let uu____24177 =
                         let uu____24184 =
                           let uu____24185 =
                             let uu____24202 =
                               let uu____24213 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24213 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24202)  in
                           FStar_Syntax_Syntax.Tm_app uu____24185  in
                         FStar_Syntax_Syntax.mk uu____24184  in
                       uu____24177 FStar_Pervasives_Native.None uu____24176
                        in
                     FStar_Pervasives_Native.Some uu____24173)))
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_res  -> effect_repr_aux false env c u_res 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_user_reflectable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_All.pipe_right quals
        (FStar_List.existsb
           (fun uu___11_24313  ->
              match uu___11_24313 with
              | FStar_Syntax_Syntax.Reflectable uu____24315 -> true
              | uu____24317 -> false))
  
let (is_total_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.TotalEffect quals
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      (is_user_reifiable_effect env effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
  
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____24377 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24392 =
        let uu____24393 = FStar_Syntax_Subst.compress t  in
        uu____24393.FStar_Syntax_Syntax.n  in
      match uu____24392 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24397,c) ->
          is_reifiable_comp env c
      | uu____24419 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24439 =
           let uu____24441 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24441  in
         if uu____24439
         then
           let uu____24444 =
             let uu____24450 =
               let uu____24452 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24452
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24450)  in
           let uu____24456 = get_range env  in
           FStar_Errors.raise_error uu____24444 uu____24456
         else ());
        (let uu____24459 = effect_repr_aux true env c u_c  in
         match uu____24459 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb =
        let uu____24492 = FStar_Syntax_Util.lids_of_sigelt s  in
        (uu____24492, s)  in
      let env1 =
        let uu___1691_24498 = env  in
        {
          solver = (uu___1691_24498.solver);
          range = (uu___1691_24498.range);
          curmodule = (uu___1691_24498.curmodule);
          gamma = (uu___1691_24498.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1691_24498.gamma_cache);
          modules = (uu___1691_24498.modules);
          expected_typ = (uu___1691_24498.expected_typ);
          sigtab = (uu___1691_24498.sigtab);
          attrtab = (uu___1691_24498.attrtab);
          instantiate_imp = (uu___1691_24498.instantiate_imp);
          effects = (uu___1691_24498.effects);
          generalize = (uu___1691_24498.generalize);
          letrecs = (uu___1691_24498.letrecs);
          top_level = (uu___1691_24498.top_level);
          check_uvars = (uu___1691_24498.check_uvars);
          use_eq = (uu___1691_24498.use_eq);
          use_eq_strict = (uu___1691_24498.use_eq_strict);
          is_iface = (uu___1691_24498.is_iface);
          admit = (uu___1691_24498.admit);
          lax = (uu___1691_24498.lax);
          lax_universes = (uu___1691_24498.lax_universes);
          phase1 = (uu___1691_24498.phase1);
          failhard = (uu___1691_24498.failhard);
          nosynth = (uu___1691_24498.nosynth);
          uvar_subtyping = (uu___1691_24498.uvar_subtyping);
          tc_term = (uu___1691_24498.tc_term);
          type_of = (uu___1691_24498.type_of);
          universe_of = (uu___1691_24498.universe_of);
          check_type_of = (uu___1691_24498.check_type_of);
          use_bv_sorts = (uu___1691_24498.use_bv_sorts);
          qtbl_name_and_index = (uu___1691_24498.qtbl_name_and_index);
          normalized_eff_names = (uu___1691_24498.normalized_eff_names);
          fv_delta_depths = (uu___1691_24498.fv_delta_depths);
          proof_ns = (uu___1691_24498.proof_ns);
          synth_hook = (uu___1691_24498.synth_hook);
          try_solve_implicits_hook =
            (uu___1691_24498.try_solve_implicits_hook);
          splice = (uu___1691_24498.splice);
          mpreprocess = (uu___1691_24498.mpreprocess);
          postprocess = (uu___1691_24498.postprocess);
          is_native_tactic = (uu___1691_24498.is_native_tactic);
          identifier_info = (uu___1691_24498.identifier_info);
          tc_hooks = (uu___1691_24498.tc_hooks);
          dsenv = (uu___1691_24498.dsenv);
          nbe = (uu___1691_24498.nbe);
          strict_args_tab = (uu___1691_24498.strict_args_tab);
          erasable_types_tab = (uu___1691_24498.erasable_types_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      env1
  
let (push_new_effect :
  env ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      -> env)
  =
  fun env  ->
    fun uu____24517  ->
      match uu____24517 with
      | (ed,quals) ->
          let effects =
            let uu___1700_24531 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1700_24531.order);
              joins = (uu___1700_24531.joins);
              polymonadic_binds = (uu___1700_24531.polymonadic_binds)
            }  in
          let uu___1703_24540 = env  in
          {
            solver = (uu___1703_24540.solver);
            range = (uu___1703_24540.range);
            curmodule = (uu___1703_24540.curmodule);
            gamma = (uu___1703_24540.gamma);
            gamma_sig = (uu___1703_24540.gamma_sig);
            gamma_cache = (uu___1703_24540.gamma_cache);
            modules = (uu___1703_24540.modules);
            expected_typ = (uu___1703_24540.expected_typ);
            sigtab = (uu___1703_24540.sigtab);
            attrtab = (uu___1703_24540.attrtab);
            instantiate_imp = (uu___1703_24540.instantiate_imp);
            effects;
            generalize = (uu___1703_24540.generalize);
            letrecs = (uu___1703_24540.letrecs);
            top_level = (uu___1703_24540.top_level);
            check_uvars = (uu___1703_24540.check_uvars);
            use_eq = (uu___1703_24540.use_eq);
            use_eq_strict = (uu___1703_24540.use_eq_strict);
            is_iface = (uu___1703_24540.is_iface);
            admit = (uu___1703_24540.admit);
            lax = (uu___1703_24540.lax);
            lax_universes = (uu___1703_24540.lax_universes);
            phase1 = (uu___1703_24540.phase1);
            failhard = (uu___1703_24540.failhard);
            nosynth = (uu___1703_24540.nosynth);
            uvar_subtyping = (uu___1703_24540.uvar_subtyping);
            tc_term = (uu___1703_24540.tc_term);
            type_of = (uu___1703_24540.type_of);
            universe_of = (uu___1703_24540.universe_of);
            check_type_of = (uu___1703_24540.check_type_of);
            use_bv_sorts = (uu___1703_24540.use_bv_sorts);
            qtbl_name_and_index = (uu___1703_24540.qtbl_name_and_index);
            normalized_eff_names = (uu___1703_24540.normalized_eff_names);
            fv_delta_depths = (uu___1703_24540.fv_delta_depths);
            proof_ns = (uu___1703_24540.proof_ns);
            synth_hook = (uu___1703_24540.synth_hook);
            try_solve_implicits_hook =
              (uu___1703_24540.try_solve_implicits_hook);
            splice = (uu___1703_24540.splice);
            mpreprocess = (uu___1703_24540.mpreprocess);
            postprocess = (uu___1703_24540.postprocess);
            is_native_tactic = (uu___1703_24540.is_native_tactic);
            identifier_info = (uu___1703_24540.identifier_info);
            tc_hooks = (uu___1703_24540.tc_hooks);
            dsenv = (uu___1703_24540.dsenv);
            nbe = (uu___1703_24540.nbe);
            strict_args_tab = (uu___1703_24540.strict_args_tab);
            erasable_types_tab = (uu___1703_24540.erasable_types_tab)
          }
  
let (exists_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * polymonadic_bind_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        let uu____24569 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24637  ->
                  match uu____24637 with
                  | (m1,n11,uu____24655,uu____24656) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24569 with
        | FStar_Pervasives_Native.Some (uu____24681,uu____24682,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24727 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24802 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24802
                  (fun uu____24823  ->
                     match uu____24823 with
                     | (c1,g1) ->
                         let uu____24834 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24834
                           (fun uu____24855  ->
                              match uu____24855 with
                              | (c2,g2) ->
                                  let uu____24866 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24866)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24988 = l1 u t e  in
                              l2 u t uu____24988))
                | uu____24989 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let edge = { msource = src; mtarget = tgt; mlift = st_mlift }  in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift }  in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____25057  ->
                    match uu____25057 with
                    | (e,uu____25065) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25088 =
            match uu____25088 with
            | (i,j) ->
                let uu____25099 = FStar_Ident.lid_equals i j  in
                if uu____25099
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _25106  -> FStar_Pervasives_Native.Some _25106)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25135 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25145 = FStar_Ident.lid_equals i k  in
                        if uu____25145
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25159 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25159
                                  then []
                                  else
                                    (let uu____25166 =
                                       let uu____25175 =
                                         find_edge order1 (i, k)  in
                                       let uu____25178 =
                                         find_edge order1 (k, j)  in
                                       (uu____25175, uu____25178)  in
                                     match uu____25166 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25193 =
                                           compose_edges e1 e2  in
                                         [uu____25193]
                                     | uu____25194 -> [])))))
                 in
              FStar_List.append order1 uu____25135  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          FStar_All.pipe_right order2
            (FStar_List.iter
               (fun edge1  ->
                  let uu____25224 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25227 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____25227
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25224
                  then
                    let uu____25234 =
                      let uu____25240 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25240)
                       in
                    let uu____25244 = get_range env  in
                    FStar_Errors.raise_error uu____25234 uu____25244
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25322 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25322
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25374 =
                                             let uu____25383 =
                                               find_edge order2 (i, k)  in
                                             let uu____25386 =
                                               find_edge order2 (j, k)  in
                                             (uu____25383, uu____25386)  in
                                           match uu____25374 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25428,uu____25429)
                                                    ->
                                                    let uu____25436 =
                                                      let uu____25443 =
                                                        let uu____25445 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25445
                                                         in
                                                      let uu____25448 =
                                                        let uu____25450 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25450
                                                         in
                                                      (uu____25443,
                                                        uu____25448)
                                                       in
                                                    (match uu____25436 with
                                                     | (true ,true ) ->
                                                         let uu____25467 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25467
                                                         then
                                                           (FStar_Errors.log_issue
                                                              FStar_Range.dummyRange
                                                              (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                "Looking multiple times at the same upper bound candidate");
                                                            bopt)
                                                         else
                                                           failwith
                                                             "Found a cycle in the lattice"
                                                     | (false ,false ) ->
                                                         bopt
                                                     | (true ,false ) ->
                                                         FStar_Pervasives_Native.Some
                                                           (k, ik, jk)
                                                     | (false ,true ) -> bopt))
                                           | uu____25510 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25562 =
                                   let uu____25564 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25564
                                     FStar_Util.is_some
                                    in
                                 if uu____25562
                                 then
                                   let uu____25613 =
                                     let uu____25619 =
                                       let uu____25621 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25623 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25625 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25627 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25621 uu____25623 uu____25625
                                         uu____25627
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25619)
                                      in
                                   FStar_Errors.raise_error uu____25613
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1824_25666 = env.effects  in
             {
               decls = (uu___1824_25666.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1824_25666.polymonadic_binds)
             }  in
           let uu___1827_25667 = env  in
           {
             solver = (uu___1827_25667.solver);
             range = (uu___1827_25667.range);
             curmodule = (uu___1827_25667.curmodule);
             gamma = (uu___1827_25667.gamma);
             gamma_sig = (uu___1827_25667.gamma_sig);
             gamma_cache = (uu___1827_25667.gamma_cache);
             modules = (uu___1827_25667.modules);
             expected_typ = (uu___1827_25667.expected_typ);
             sigtab = (uu___1827_25667.sigtab);
             attrtab = (uu___1827_25667.attrtab);
             instantiate_imp = (uu___1827_25667.instantiate_imp);
             effects;
             generalize = (uu___1827_25667.generalize);
             letrecs = (uu___1827_25667.letrecs);
             top_level = (uu___1827_25667.top_level);
             check_uvars = (uu___1827_25667.check_uvars);
             use_eq = (uu___1827_25667.use_eq);
             use_eq_strict = (uu___1827_25667.use_eq_strict);
             is_iface = (uu___1827_25667.is_iface);
             admit = (uu___1827_25667.admit);
             lax = (uu___1827_25667.lax);
             lax_universes = (uu___1827_25667.lax_universes);
             phase1 = (uu___1827_25667.phase1);
             failhard = (uu___1827_25667.failhard);
             nosynth = (uu___1827_25667.nosynth);
             uvar_subtyping = (uu___1827_25667.uvar_subtyping);
             tc_term = (uu___1827_25667.tc_term);
             type_of = (uu___1827_25667.type_of);
             universe_of = (uu___1827_25667.universe_of);
             check_type_of = (uu___1827_25667.check_type_of);
             use_bv_sorts = (uu___1827_25667.use_bv_sorts);
             qtbl_name_and_index = (uu___1827_25667.qtbl_name_and_index);
             normalized_eff_names = (uu___1827_25667.normalized_eff_names);
             fv_delta_depths = (uu___1827_25667.fv_delta_depths);
             proof_ns = (uu___1827_25667.proof_ns);
             synth_hook = (uu___1827_25667.synth_hook);
             try_solve_implicits_hook =
               (uu___1827_25667.try_solve_implicits_hook);
             splice = (uu___1827_25667.splice);
             mpreprocess = (uu___1827_25667.mpreprocess);
             postprocess = (uu___1827_25667.postprocess);
             is_native_tactic = (uu___1827_25667.is_native_tactic);
             identifier_info = (uu___1827_25667.identifier_info);
             tc_hooks = (uu___1827_25667.tc_hooks);
             dsenv = (uu___1827_25667.dsenv);
             nbe = (uu___1827_25667.nbe);
             strict_args_tab = (uu___1827_25667.strict_args_tab);
             erasable_types_tab = (uu___1827_25667.erasable_types_tab)
           })
  
let (add_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Ident.lident -> polymonadic_bind_t -> env)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ty  ->
            let err_msg poly =
              let uu____25715 = FStar_Ident.string_of_lid m  in
              let uu____25717 = FStar_Ident.string_of_lid n1  in
              let uu____25719 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25715 uu____25717 uu____25719
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25728 =
              let uu____25730 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____25730 FStar_Util.is_some  in
            if uu____25728
            then
              let uu____25767 =
                let uu____25773 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25773)
                 in
              FStar_Errors.raise_error uu____25767 env.range
            else
              (let uu____25779 =
                 let uu____25781 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25781 FStar_Util.is_some  in
               if uu____25779
               then
                 let uu____25806 =
                   let uu____25812 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25812)
                    in
                 FStar_Errors.raise_error uu____25806 env.range
               else
                 (let uu___1842_25818 = env  in
                  {
                    solver = (uu___1842_25818.solver);
                    range = (uu___1842_25818.range);
                    curmodule = (uu___1842_25818.curmodule);
                    gamma = (uu___1842_25818.gamma);
                    gamma_sig = (uu___1842_25818.gamma_sig);
                    gamma_cache = (uu___1842_25818.gamma_cache);
                    modules = (uu___1842_25818.modules);
                    expected_typ = (uu___1842_25818.expected_typ);
                    sigtab = (uu___1842_25818.sigtab);
                    attrtab = (uu___1842_25818.attrtab);
                    instantiate_imp = (uu___1842_25818.instantiate_imp);
                    effects =
                      (let uu___1844_25820 = env.effects  in
                       {
                         decls = (uu___1844_25820.decls);
                         order = (uu___1844_25820.order);
                         joins = (uu___1844_25820.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1842_25818.generalize);
                    letrecs = (uu___1842_25818.letrecs);
                    top_level = (uu___1842_25818.top_level);
                    check_uvars = (uu___1842_25818.check_uvars);
                    use_eq = (uu___1842_25818.use_eq);
                    use_eq_strict = (uu___1842_25818.use_eq_strict);
                    is_iface = (uu___1842_25818.is_iface);
                    admit = (uu___1842_25818.admit);
                    lax = (uu___1842_25818.lax);
                    lax_universes = (uu___1842_25818.lax_universes);
                    phase1 = (uu___1842_25818.phase1);
                    failhard = (uu___1842_25818.failhard);
                    nosynth = (uu___1842_25818.nosynth);
                    uvar_subtyping = (uu___1842_25818.uvar_subtyping);
                    tc_term = (uu___1842_25818.tc_term);
                    type_of = (uu___1842_25818.type_of);
                    universe_of = (uu___1842_25818.universe_of);
                    check_type_of = (uu___1842_25818.check_type_of);
                    use_bv_sorts = (uu___1842_25818.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1842_25818.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1842_25818.normalized_eff_names);
                    fv_delta_depths = (uu___1842_25818.fv_delta_depths);
                    proof_ns = (uu___1842_25818.proof_ns);
                    synth_hook = (uu___1842_25818.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1842_25818.try_solve_implicits_hook);
                    splice = (uu___1842_25818.splice);
                    mpreprocess = (uu___1842_25818.mpreprocess);
                    postprocess = (uu___1842_25818.postprocess);
                    is_native_tactic = (uu___1842_25818.is_native_tactic);
                    identifier_info = (uu___1842_25818.identifier_info);
                    tc_hooks = (uu___1842_25818.tc_hooks);
                    dsenv = (uu___1842_25818.dsenv);
                    nbe = (uu___1842_25818.nbe);
                    strict_args_tab = (uu___1842_25818.strict_args_tab);
                    erasable_types_tab = (uu___1842_25818.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1848_25892 = env  in
      {
        solver = (uu___1848_25892.solver);
        range = (uu___1848_25892.range);
        curmodule = (uu___1848_25892.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1848_25892.gamma_sig);
        gamma_cache = (uu___1848_25892.gamma_cache);
        modules = (uu___1848_25892.modules);
        expected_typ = (uu___1848_25892.expected_typ);
        sigtab = (uu___1848_25892.sigtab);
        attrtab = (uu___1848_25892.attrtab);
        instantiate_imp = (uu___1848_25892.instantiate_imp);
        effects = (uu___1848_25892.effects);
        generalize = (uu___1848_25892.generalize);
        letrecs = (uu___1848_25892.letrecs);
        top_level = (uu___1848_25892.top_level);
        check_uvars = (uu___1848_25892.check_uvars);
        use_eq = (uu___1848_25892.use_eq);
        use_eq_strict = (uu___1848_25892.use_eq_strict);
        is_iface = (uu___1848_25892.is_iface);
        admit = (uu___1848_25892.admit);
        lax = (uu___1848_25892.lax);
        lax_universes = (uu___1848_25892.lax_universes);
        phase1 = (uu___1848_25892.phase1);
        failhard = (uu___1848_25892.failhard);
        nosynth = (uu___1848_25892.nosynth);
        uvar_subtyping = (uu___1848_25892.uvar_subtyping);
        tc_term = (uu___1848_25892.tc_term);
        type_of = (uu___1848_25892.type_of);
        universe_of = (uu___1848_25892.universe_of);
        check_type_of = (uu___1848_25892.check_type_of);
        use_bv_sorts = (uu___1848_25892.use_bv_sorts);
        qtbl_name_and_index = (uu___1848_25892.qtbl_name_and_index);
        normalized_eff_names = (uu___1848_25892.normalized_eff_names);
        fv_delta_depths = (uu___1848_25892.fv_delta_depths);
        proof_ns = (uu___1848_25892.proof_ns);
        synth_hook = (uu___1848_25892.synth_hook);
        try_solve_implicits_hook = (uu___1848_25892.try_solve_implicits_hook);
        splice = (uu___1848_25892.splice);
        mpreprocess = (uu___1848_25892.mpreprocess);
        postprocess = (uu___1848_25892.postprocess);
        is_native_tactic = (uu___1848_25892.is_native_tactic);
        identifier_info = (uu___1848_25892.identifier_info);
        tc_hooks = (uu___1848_25892.tc_hooks);
        dsenv = (uu___1848_25892.dsenv);
        nbe = (uu___1848_25892.nbe);
        strict_args_tab = (uu___1848_25892.strict_args_tab);
        erasable_types_tab = (uu___1848_25892.erasable_types_tab)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env -> (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option) =
  fun env  ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___1861_25950 = env  in
             {
               solver = (uu___1861_25950.solver);
               range = (uu___1861_25950.range);
               curmodule = (uu___1861_25950.curmodule);
               gamma = rest;
               gamma_sig = (uu___1861_25950.gamma_sig);
               gamma_cache = (uu___1861_25950.gamma_cache);
               modules = (uu___1861_25950.modules);
               expected_typ = (uu___1861_25950.expected_typ);
               sigtab = (uu___1861_25950.sigtab);
               attrtab = (uu___1861_25950.attrtab);
               instantiate_imp = (uu___1861_25950.instantiate_imp);
               effects = (uu___1861_25950.effects);
               generalize = (uu___1861_25950.generalize);
               letrecs = (uu___1861_25950.letrecs);
               top_level = (uu___1861_25950.top_level);
               check_uvars = (uu___1861_25950.check_uvars);
               use_eq = (uu___1861_25950.use_eq);
               use_eq_strict = (uu___1861_25950.use_eq_strict);
               is_iface = (uu___1861_25950.is_iface);
               admit = (uu___1861_25950.admit);
               lax = (uu___1861_25950.lax);
               lax_universes = (uu___1861_25950.lax_universes);
               phase1 = (uu___1861_25950.phase1);
               failhard = (uu___1861_25950.failhard);
               nosynth = (uu___1861_25950.nosynth);
               uvar_subtyping = (uu___1861_25950.uvar_subtyping);
               tc_term = (uu___1861_25950.tc_term);
               type_of = (uu___1861_25950.type_of);
               universe_of = (uu___1861_25950.universe_of);
               check_type_of = (uu___1861_25950.check_type_of);
               use_bv_sorts = (uu___1861_25950.use_bv_sorts);
               qtbl_name_and_index = (uu___1861_25950.qtbl_name_and_index);
               normalized_eff_names = (uu___1861_25950.normalized_eff_names);
               fv_delta_depths = (uu___1861_25950.fv_delta_depths);
               proof_ns = (uu___1861_25950.proof_ns);
               synth_hook = (uu___1861_25950.synth_hook);
               try_solve_implicits_hook =
                 (uu___1861_25950.try_solve_implicits_hook);
               splice = (uu___1861_25950.splice);
               mpreprocess = (uu___1861_25950.mpreprocess);
               postprocess = (uu___1861_25950.postprocess);
               is_native_tactic = (uu___1861_25950.is_native_tactic);
               identifier_info = (uu___1861_25950.identifier_info);
               tc_hooks = (uu___1861_25950.tc_hooks);
               dsenv = (uu___1861_25950.dsenv);
               nbe = (uu___1861_25950.nbe);
               strict_args_tab = (uu___1861_25950.strict_args_tab);
               erasable_types_tab = (uu___1861_25950.erasable_types_tab)
             }))
    | uu____25951 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____25980  ->
             match uu____25980 with | (x,uu____25988) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___1875_26023 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1875_26023.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1875_26023.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun x  ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
  
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term
          Prims.list))
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____26096 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26096 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____26124 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26124)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1896_26140 = env  in
      {
        solver = (uu___1896_26140.solver);
        range = (uu___1896_26140.range);
        curmodule = (uu___1896_26140.curmodule);
        gamma = (uu___1896_26140.gamma);
        gamma_sig = (uu___1896_26140.gamma_sig);
        gamma_cache = (uu___1896_26140.gamma_cache);
        modules = (uu___1896_26140.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1896_26140.sigtab);
        attrtab = (uu___1896_26140.attrtab);
        instantiate_imp = (uu___1896_26140.instantiate_imp);
        effects = (uu___1896_26140.effects);
        generalize = (uu___1896_26140.generalize);
        letrecs = (uu___1896_26140.letrecs);
        top_level = (uu___1896_26140.top_level);
        check_uvars = (uu___1896_26140.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1896_26140.use_eq_strict);
        is_iface = (uu___1896_26140.is_iface);
        admit = (uu___1896_26140.admit);
        lax = (uu___1896_26140.lax);
        lax_universes = (uu___1896_26140.lax_universes);
        phase1 = (uu___1896_26140.phase1);
        failhard = (uu___1896_26140.failhard);
        nosynth = (uu___1896_26140.nosynth);
        uvar_subtyping = (uu___1896_26140.uvar_subtyping);
        tc_term = (uu___1896_26140.tc_term);
        type_of = (uu___1896_26140.type_of);
        universe_of = (uu___1896_26140.universe_of);
        check_type_of = (uu___1896_26140.check_type_of);
        use_bv_sorts = (uu___1896_26140.use_bv_sorts);
        qtbl_name_and_index = (uu___1896_26140.qtbl_name_and_index);
        normalized_eff_names = (uu___1896_26140.normalized_eff_names);
        fv_delta_depths = (uu___1896_26140.fv_delta_depths);
        proof_ns = (uu___1896_26140.proof_ns);
        synth_hook = (uu___1896_26140.synth_hook);
        try_solve_implicits_hook = (uu___1896_26140.try_solve_implicits_hook);
        splice = (uu___1896_26140.splice);
        mpreprocess = (uu___1896_26140.mpreprocess);
        postprocess = (uu___1896_26140.postprocess);
        is_native_tactic = (uu___1896_26140.is_native_tactic);
        identifier_info = (uu___1896_26140.identifier_info);
        tc_hooks = (uu___1896_26140.tc_hooks);
        dsenv = (uu___1896_26140.dsenv);
        nbe = (uu___1896_26140.nbe);
        strict_args_tab = (uu___1896_26140.strict_args_tab);
        erasable_types_tab = (uu___1896_26140.erasable_types_tab)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env -> (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)) =
  fun env_  ->
    let uu____26171 = expected_typ env_  in
    ((let uu___1903_26177 = env_  in
      {
        solver = (uu___1903_26177.solver);
        range = (uu___1903_26177.range);
        curmodule = (uu___1903_26177.curmodule);
        gamma = (uu___1903_26177.gamma);
        gamma_sig = (uu___1903_26177.gamma_sig);
        gamma_cache = (uu___1903_26177.gamma_cache);
        modules = (uu___1903_26177.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1903_26177.sigtab);
        attrtab = (uu___1903_26177.attrtab);
        instantiate_imp = (uu___1903_26177.instantiate_imp);
        effects = (uu___1903_26177.effects);
        generalize = (uu___1903_26177.generalize);
        letrecs = (uu___1903_26177.letrecs);
        top_level = (uu___1903_26177.top_level);
        check_uvars = (uu___1903_26177.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1903_26177.use_eq_strict);
        is_iface = (uu___1903_26177.is_iface);
        admit = (uu___1903_26177.admit);
        lax = (uu___1903_26177.lax);
        lax_universes = (uu___1903_26177.lax_universes);
        phase1 = (uu___1903_26177.phase1);
        failhard = (uu___1903_26177.failhard);
        nosynth = (uu___1903_26177.nosynth);
        uvar_subtyping = (uu___1903_26177.uvar_subtyping);
        tc_term = (uu___1903_26177.tc_term);
        type_of = (uu___1903_26177.type_of);
        universe_of = (uu___1903_26177.universe_of);
        check_type_of = (uu___1903_26177.check_type_of);
        use_bv_sorts = (uu___1903_26177.use_bv_sorts);
        qtbl_name_and_index = (uu___1903_26177.qtbl_name_and_index);
        normalized_eff_names = (uu___1903_26177.normalized_eff_names);
        fv_delta_depths = (uu___1903_26177.fv_delta_depths);
        proof_ns = (uu___1903_26177.proof_ns);
        synth_hook = (uu___1903_26177.synth_hook);
        try_solve_implicits_hook = (uu___1903_26177.try_solve_implicits_hook);
        splice = (uu___1903_26177.splice);
        mpreprocess = (uu___1903_26177.mpreprocess);
        postprocess = (uu___1903_26177.postprocess);
        is_native_tactic = (uu___1903_26177.is_native_tactic);
        identifier_info = (uu___1903_26177.identifier_info);
        tc_hooks = (uu___1903_26177.tc_hooks);
        dsenv = (uu___1903_26177.dsenv);
        nbe = (uu___1903_26177.nbe);
        strict_args_tab = (uu___1903_26177.strict_args_tab);
        erasable_types_tab = (uu___1903_26177.erasable_types_tab)
      }), uu____26171)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26189 =
      let uu____26192 = FStar_Ident.id_of_text ""  in [uu____26192]  in
    FStar_Ident.lid_of_ids uu____26189  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____26199 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26199
        then
          let uu____26204 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26204 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1911_26232 = env  in
       {
         solver = (uu___1911_26232.solver);
         range = (uu___1911_26232.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1911_26232.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1911_26232.expected_typ);
         sigtab = (uu___1911_26232.sigtab);
         attrtab = (uu___1911_26232.attrtab);
         instantiate_imp = (uu___1911_26232.instantiate_imp);
         effects = (uu___1911_26232.effects);
         generalize = (uu___1911_26232.generalize);
         letrecs = (uu___1911_26232.letrecs);
         top_level = (uu___1911_26232.top_level);
         check_uvars = (uu___1911_26232.check_uvars);
         use_eq = (uu___1911_26232.use_eq);
         use_eq_strict = (uu___1911_26232.use_eq_strict);
         is_iface = (uu___1911_26232.is_iface);
         admit = (uu___1911_26232.admit);
         lax = (uu___1911_26232.lax);
         lax_universes = (uu___1911_26232.lax_universes);
         phase1 = (uu___1911_26232.phase1);
         failhard = (uu___1911_26232.failhard);
         nosynth = (uu___1911_26232.nosynth);
         uvar_subtyping = (uu___1911_26232.uvar_subtyping);
         tc_term = (uu___1911_26232.tc_term);
         type_of = (uu___1911_26232.type_of);
         universe_of = (uu___1911_26232.universe_of);
         check_type_of = (uu___1911_26232.check_type_of);
         use_bv_sorts = (uu___1911_26232.use_bv_sorts);
         qtbl_name_and_index = (uu___1911_26232.qtbl_name_and_index);
         normalized_eff_names = (uu___1911_26232.normalized_eff_names);
         fv_delta_depths = (uu___1911_26232.fv_delta_depths);
         proof_ns = (uu___1911_26232.proof_ns);
         synth_hook = (uu___1911_26232.synth_hook);
         try_solve_implicits_hook =
           (uu___1911_26232.try_solve_implicits_hook);
         splice = (uu___1911_26232.splice);
         mpreprocess = (uu___1911_26232.mpreprocess);
         postprocess = (uu___1911_26232.postprocess);
         is_native_tactic = (uu___1911_26232.is_native_tactic);
         identifier_info = (uu___1911_26232.identifier_info);
         tc_hooks = (uu___1911_26232.tc_hooks);
         dsenv = (uu___1911_26232.dsenv);
         nbe = (uu___1911_26232.nbe);
         strict_args_tab = (uu___1911_26232.strict_args_tab);
         erasable_types_tab = (uu___1911_26232.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26284)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26288,(uu____26289,t)))::tl1
          ->
          let uu____26310 =
            let uu____26313 = FStar_Syntax_Free.uvars t  in
            ext out uu____26313  in
          aux uu____26310 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26316;
            FStar_Syntax_Syntax.index = uu____26317;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26325 =
            let uu____26328 = FStar_Syntax_Free.uvars t  in
            ext out uu____26328  in
          aux uu____26325 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26386)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26390,(uu____26391,t)))::tl1
          ->
          let uu____26412 =
            let uu____26415 = FStar_Syntax_Free.univs t  in
            ext out uu____26415  in
          aux uu____26412 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26418;
            FStar_Syntax_Syntax.index = uu____26419;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26427 =
            let uu____26430 = FStar_Syntax_Free.univs t  in
            ext out uu____26430  in
          aux uu____26427 tl1
       in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____26492 = FStar_Util.set_add uname out  in
          aux uu____26492 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26495,(uu____26496,t)))::tl1
          ->
          let uu____26517 =
            let uu____26520 = FStar_Syntax_Free.univnames t  in
            ext out uu____26520  in
          aux uu____26517 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26523;
            FStar_Syntax_Syntax.index = uu____26524;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26532 =
            let uu____26535 = FStar_Syntax_Free.univnames t  in
            ext out uu____26535  in
          aux uu____26532 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26556  ->
            match uu___12_26556 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26560 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26573 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26584 =
      let uu____26593 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26593
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26584 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26641 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26654  ->
              match uu___13_26654 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26657 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26657
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26663) ->
                  let uu____26680 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26680))
       in
    FStar_All.pipe_right uu____26641 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26694  ->
    match uu___14_26694 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26700 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26700
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____26724  ->
         fun v1  ->
           fun keys1  ->
             let uu____26730 = FStar_Syntax_Util.lids_of_sigelt v1  in
             FStar_List.append uu____26730 keys1) keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26782) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26815,uu____26816) -> false  in
      let uu____26830 =
        FStar_List.tryFind
          (fun uu____26852  ->
             match uu____26852 with | (p,uu____26863) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26830 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26882,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26912 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26912
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2054_26934 = e  in
        {
          solver = (uu___2054_26934.solver);
          range = (uu___2054_26934.range);
          curmodule = (uu___2054_26934.curmodule);
          gamma = (uu___2054_26934.gamma);
          gamma_sig = (uu___2054_26934.gamma_sig);
          gamma_cache = (uu___2054_26934.gamma_cache);
          modules = (uu___2054_26934.modules);
          expected_typ = (uu___2054_26934.expected_typ);
          sigtab = (uu___2054_26934.sigtab);
          attrtab = (uu___2054_26934.attrtab);
          instantiate_imp = (uu___2054_26934.instantiate_imp);
          effects = (uu___2054_26934.effects);
          generalize = (uu___2054_26934.generalize);
          letrecs = (uu___2054_26934.letrecs);
          top_level = (uu___2054_26934.top_level);
          check_uvars = (uu___2054_26934.check_uvars);
          use_eq = (uu___2054_26934.use_eq);
          use_eq_strict = (uu___2054_26934.use_eq_strict);
          is_iface = (uu___2054_26934.is_iface);
          admit = (uu___2054_26934.admit);
          lax = (uu___2054_26934.lax);
          lax_universes = (uu___2054_26934.lax_universes);
          phase1 = (uu___2054_26934.phase1);
          failhard = (uu___2054_26934.failhard);
          nosynth = (uu___2054_26934.nosynth);
          uvar_subtyping = (uu___2054_26934.uvar_subtyping);
          tc_term = (uu___2054_26934.tc_term);
          type_of = (uu___2054_26934.type_of);
          universe_of = (uu___2054_26934.universe_of);
          check_type_of = (uu___2054_26934.check_type_of);
          use_bv_sorts = (uu___2054_26934.use_bv_sorts);
          qtbl_name_and_index = (uu___2054_26934.qtbl_name_and_index);
          normalized_eff_names = (uu___2054_26934.normalized_eff_names);
          fv_delta_depths = (uu___2054_26934.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2054_26934.synth_hook);
          try_solve_implicits_hook =
            (uu___2054_26934.try_solve_implicits_hook);
          splice = (uu___2054_26934.splice);
          mpreprocess = (uu___2054_26934.mpreprocess);
          postprocess = (uu___2054_26934.postprocess);
          is_native_tactic = (uu___2054_26934.is_native_tactic);
          identifier_info = (uu___2054_26934.identifier_info);
          tc_hooks = (uu___2054_26934.tc_hooks);
          dsenv = (uu___2054_26934.dsenv);
          nbe = (uu___2054_26934.nbe);
          strict_args_tab = (uu___2054_26934.strict_args_tab);
          erasable_types_tab = (uu___2054_26934.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2063_26982 = e  in
      {
        solver = (uu___2063_26982.solver);
        range = (uu___2063_26982.range);
        curmodule = (uu___2063_26982.curmodule);
        gamma = (uu___2063_26982.gamma);
        gamma_sig = (uu___2063_26982.gamma_sig);
        gamma_cache = (uu___2063_26982.gamma_cache);
        modules = (uu___2063_26982.modules);
        expected_typ = (uu___2063_26982.expected_typ);
        sigtab = (uu___2063_26982.sigtab);
        attrtab = (uu___2063_26982.attrtab);
        instantiate_imp = (uu___2063_26982.instantiate_imp);
        effects = (uu___2063_26982.effects);
        generalize = (uu___2063_26982.generalize);
        letrecs = (uu___2063_26982.letrecs);
        top_level = (uu___2063_26982.top_level);
        check_uvars = (uu___2063_26982.check_uvars);
        use_eq = (uu___2063_26982.use_eq);
        use_eq_strict = (uu___2063_26982.use_eq_strict);
        is_iface = (uu___2063_26982.is_iface);
        admit = (uu___2063_26982.admit);
        lax = (uu___2063_26982.lax);
        lax_universes = (uu___2063_26982.lax_universes);
        phase1 = (uu___2063_26982.phase1);
        failhard = (uu___2063_26982.failhard);
        nosynth = (uu___2063_26982.nosynth);
        uvar_subtyping = (uu___2063_26982.uvar_subtyping);
        tc_term = (uu___2063_26982.tc_term);
        type_of = (uu___2063_26982.type_of);
        universe_of = (uu___2063_26982.universe_of);
        check_type_of = (uu___2063_26982.check_type_of);
        use_bv_sorts = (uu___2063_26982.use_bv_sorts);
        qtbl_name_and_index = (uu___2063_26982.qtbl_name_and_index);
        normalized_eff_names = (uu___2063_26982.normalized_eff_names);
        fv_delta_depths = (uu___2063_26982.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2063_26982.synth_hook);
        try_solve_implicits_hook = (uu___2063_26982.try_solve_implicits_hook);
        splice = (uu___2063_26982.splice);
        mpreprocess = (uu___2063_26982.mpreprocess);
        postprocess = (uu___2063_26982.postprocess);
        is_native_tactic = (uu___2063_26982.is_native_tactic);
        identifier_info = (uu___2063_26982.identifier_info);
        tc_hooks = (uu___2063_26982.tc_hooks);
        dsenv = (uu___2063_26982.dsenv);
        nbe = (uu___2063_26982.nbe);
        strict_args_tab = (uu___2063_26982.strict_args_tab);
        erasable_types_tab = (uu___2063_26982.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26998 = FStar_Syntax_Free.names t  in
      let uu____27001 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26998 uu____27001
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____27024 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____27024
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____27034 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____27034
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____27055 =
      match uu____27055 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27075 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27075)
       in
    let uu____27083 =
      let uu____27087 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____27087 FStar_List.rev  in
    FStar_All.pipe_right uu____27083 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Common.guard_f = g;
      FStar_TypeChecker_Common.deferred = [];
      FStar_TypeChecker_Common.univ_ineqs = ([], []);
      FStar_TypeChecker_Common.implicits = []
    }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.FStar_TypeChecker_Common.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = [];
        FStar_TypeChecker_Common.univ_ineqs = ([],[]);
        FStar_TypeChecker_Common.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check
                   = FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____27155 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27155 with
                   | FStar_Pervasives_Native.Some uu____27159 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27162 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27172;
        FStar_TypeChecker_Common.univ_ineqs = uu____27173;
        FStar_TypeChecker_Common.implicits = uu____27174;_} -> true
    | uu____27184 -> false
  
let (trivial_guard : guard_t) = FStar_TypeChecker_Common.trivial_guard 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___2107_27206 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2107_27206.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2107_27206.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2107_27206.FStar_TypeChecker_Common.implicits)
          }
  
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____27245 = FStar_Options.defensive ()  in
          if uu____27245
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27251 =
              let uu____27253 =
                let uu____27255 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27255  in
              Prims.op_Negation uu____27253  in
            (if uu____27251
             then
               let uu____27262 =
                 let uu____27268 =
                   let uu____27270 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27272 =
                     let uu____27274 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27274
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27270 uu____27272
                    in
                 (FStar_Errors.Warning_Defensive, uu____27268)  in
               FStar_Errors.log_issue rng uu____27262
             else ())
          else ()
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____27314 =
            let uu____27316 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27316  in
          if uu____27314
          then ()
          else
            (let uu____27321 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27321 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27347 =
            let uu____27349 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27349  in
          if uu____27347
          then ()
          else
            (let uu____27354 = bound_vars e  in
             def_check_closed_in rng msg uu____27354 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.FStar_TypeChecker_Common.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2144_27393 = g  in
          let uu____27394 =
            let uu____27395 =
              let uu____27396 =
                let uu____27403 =
                  let uu____27404 =
                    let uu____27421 =
                      let uu____27432 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27432]  in
                    (f, uu____27421)  in
                  FStar_Syntax_Syntax.Tm_app uu____27404  in
                FStar_Syntax_Syntax.mk uu____27403  in
              uu____27396 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27469  -> FStar_TypeChecker_Common.NonTrivial _27469)
              uu____27395
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27394;
            FStar_TypeChecker_Common.deferred =
              (uu___2144_27393.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2144_27393.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2144_27393.FStar_TypeChecker_Common.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2151_27487 = g  in
          let uu____27488 =
            let uu____27489 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27489  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27488;
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27487.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27487.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27487.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2156_27506 = g  in
          let uu____27507 =
            let uu____27508 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27508  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27507;
            FStar_TypeChecker_Common.deferred =
              (uu___2156_27506.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_27506.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_27506.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2160_27510 = g  in
          let uu____27511 =
            let uu____27512 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27512  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27511;
            FStar_TypeChecker_Common.deferred =
              (uu___2160_27510.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2160_27510.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2160_27510.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27519 ->
        failwith "impossible"
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  -> FStar_TypeChecker_Common.check_trivial t 
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> FStar_TypeChecker_Common.conj_guard g1 g2 
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_TypeChecker_Common.conj_guards gs 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> FStar_TypeChecker_Common.imp_guard g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____27596 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27596
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2183_27603 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2183_27603.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2183_27603.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2183_27603.FStar_TypeChecker_Common.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____27637 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27637
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2198_27664 = g  in
            let uu____27665 =
              let uu____27666 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27666  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27665;
              FStar_TypeChecker_Common.deferred =
                (uu___2198_27664.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2198_27664.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2198_27664.FStar_TypeChecker_Common.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Dyn.dyn * FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
                FStar_Range.range) Prims.list * guard_t))
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            fun meta  ->
              let uu____27724 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27724 with
              | FStar_Pervasives_Native.Some
                  (uu____27749::(tm,uu____27751)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27815 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27833 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27833;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    }  in
                  (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                     true gamma binders;
                   (let t =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_uvar
                           (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                        FStar_Pervasives_Native.None r
                       in
                    let imp =
                      {
                        FStar_TypeChecker_Common.imp_reason = reason;
                        FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                        FStar_TypeChecker_Common.imp_tm = t;
                        FStar_TypeChecker_Common.imp_range = r
                      }  in
                    let g =
                      let uu___2220_27865 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2220_27865.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2220_27865.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2220_27865.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (uvars_for_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.subst_t ->
        (FStar_Syntax_Syntax.binder -> Prims.string) ->
          FStar_Range.range ->
            (FStar_Syntax_Syntax.term Prims.list * guard_t))
  =
  fun env  ->
    fun bs  ->
      fun substs  ->
        fun reason  ->
          fun r  ->
            let uu____27919 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27976  ->
                      fun b  ->
                        match uu____27976 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____28018 =
                              let uu____28031 = reason b  in
                              new_implicit_var_aux uu____28031 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____28018 with
                             | (t,uu____28048,g_t) ->
                                 let uu____28062 =
                                   let uu____28065 =
                                     let uu____28068 =
                                       let uu____28069 =
                                         let uu____28076 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28076, t)  in
                                       FStar_Syntax_Syntax.NT uu____28069  in
                                     [uu____28068]  in
                                   FStar_List.append substs1 uu____28065  in
                                 let uu____28087 = conj_guard g g_t  in
                                 (uu____28062,
                                   (FStar_List.append uvars1 [t]),
                                   uu____28087))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27919
              (fun uu____28116  ->
                 match uu____28116 with
                 | (uu____28133,uvars1,g) -> (uvars1, g))
  
let (pure_precondition_for_trivial_post :
  env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        fun wp  ->
          fun r  ->
            let trivial_post =
              let post_ts =
                let uu____28174 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28174 FStar_Util.must  in
              let uu____28191 = inst_tscheme_with post_ts [u]  in
              match uu____28191 with
              | (uu____28196,post) ->
                  let uu____28198 =
                    let uu____28203 =
                      let uu____28204 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28204]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28203  in
                  uu____28198 FStar_Pervasives_Native.None r
               in
            let uu____28237 =
              let uu____28242 =
                let uu____28243 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28243]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28242  in
            uu____28237 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28279  -> ());
    push = (fun uu____28281  -> ());
    pop = (fun uu____28284  -> ());
    snapshot =
      (fun uu____28287  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28306  -> fun uu____28307  -> ());
    encode_sig = (fun uu____28322  -> fun uu____28323  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28329 =
             let uu____28336 = FStar_Options.peek ()  in (e, g, uu____28336)
              in
           [uu____28329]);
    solve = (fun uu____28352  -> fun uu____28353  -> fun uu____28354  -> ());
    finish = (fun uu____28361  -> ());
    refresh = (fun uu____28363  -> ())
  } 