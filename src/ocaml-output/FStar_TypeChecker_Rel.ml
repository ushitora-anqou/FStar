open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f  ->
    let uf = FStar_Syntax_Unionfind.get ()  in
    FStar_Thunk.mk
      (fun uu____40  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         FStar_Syntax_Unionfind.set uf;
         (let r = f ()  in FStar_Syntax_Unionfind.rollback tx; r))
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____78 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____113 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Common.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Dyn.dyn * FStar_Syntax_Syntax.term'
                  FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option
                  ->
                  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
                    worklist))
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check1  ->
                fun meta  ->
                  let ctx_uvar =
                    let uu____570 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____570;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check1;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    }  in
                  FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                    true gamma binders;
                  (let t =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_uvar
                          (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange))) r
                      in
                   let imp =
                     {
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     }  in
                   (let uu____602 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____602
                    then
                      let uu____606 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____606
                    else ());
                   (ctx_uvar, t,
                     ((let uu___80_612 = wl  in
                       {
                         attempting = (uu___80_612.attempting);
                         wl_deferred = (uu___80_612.wl_deferred);
                         ctr = (uu___80_612.ctr);
                         defer_ok = (uu___80_612.defer_ok);
                         smt_ok = (uu___80_612.smt_ok);
                         umax_heuristic_ok = (uu___80_612.umax_heuristic_ok);
                         tcenv = (uu___80_612.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits))
                       }))))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
            worklist))
  =
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___86_645 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___86_645.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___86_645.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___86_645.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___86_645.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___86_645.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___86_645.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___86_645.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___86_645.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___86_645.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___86_645.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___86_645.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___86_645.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___86_645.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___86_645.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___86_645.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___86_645.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___86_645.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___86_645.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___86_645.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___86_645.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___86_645.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___86_645.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___86_645.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___86_645.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___86_645.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___86_645.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___86_645.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___86_645.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___86_645.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___86_645.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___86_645.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___86_645.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___86_645.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___86_645.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___86_645.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___86_645.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___86_645.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___86_645.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___86_645.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___86_645.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___86_645.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___86_645.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___86_645.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___86_645.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___86_645.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___86_645.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____647 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____647 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____734 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____769 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____799 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____810 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____821 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_839  ->
    match uu___0_839 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____851 = FStar_Syntax_Util.head_and_args t  in
    match uu____851 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____914 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____916 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____931 =
                     let uu____933 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____933  in
                   FStar_Util.format1 "@<%s>" uu____931
                in
             let uu____937 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____914 uu____916 uu____937
         | uu____940 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_952  ->
      match uu___1_952 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____957 =
            let uu____961 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____963 =
              let uu____967 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____969 =
                let uu____973 =
                  let uu____977 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____977]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____973
                 in
              uu____967 :: uu____969  in
            uu____961 :: uu____963  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____957
      | FStar_TypeChecker_Common.CProb p ->
          let uu____988 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____990 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____992 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____988 uu____990
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____992
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1006  ->
      match uu___2_1006 with
      | UNIV (u,t) ->
          let x =
            let uu____1012 = FStar_Options.hide_uvar_nums ()  in
            if uu____1012
            then "?"
            else
              (let uu____1019 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1019 FStar_Util.string_of_int)
             in
          let uu____1023 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1023
      | TERM (u,t) ->
          let x =
            let uu____1030 = FStar_Options.hide_uvar_nums ()  in
            if uu____1030
            then "?"
            else
              (let uu____1037 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1037 FStar_Util.string_of_int)
             in
          let uu____1041 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s <- %s" x uu____1041
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  -> FStar_Common.string_of_list (uvi_to_string env) uvis
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1071 =
      let uu____1075 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1075
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1071 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1094 .
    (FStar_Syntax_Syntax.term * 'Auu____1094) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1113 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1134  ->
              match uu____1134 with
              | (x,uu____1141) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1113 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = Prims.int_zero;
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1181 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1181
         then
           let uu____1186 = FStar_Thunk.force reason  in
           let uu____1189 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1186 uu____1189
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1212 = mklstr (fun uu____1215  -> reason)  in
        giveup env uu____1212 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1221  ->
    match uu___3_1221 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1227 .
    'Auu____1227 FStar_TypeChecker_Common.problem ->
      'Auu____1227 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___150_1239 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___150_1239.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___150_1239.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___150_1239.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___150_1239.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___150_1239.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___150_1239.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___150_1239.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1247 .
    'Auu____1247 FStar_TypeChecker_Common.problem ->
      'Auu____1247 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1267  ->
    match uu___4_1267 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1273  -> FStar_TypeChecker_Common.TProb _1273)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1279  -> FStar_TypeChecker_Common.CProb _1279)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1285  ->
    match uu___5_1285 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___162_1291 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___162_1291.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___162_1291.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___162_1291.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___162_1291.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___162_1291.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___162_1291.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___162_1291.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___162_1291.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___162_1291.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___166_1299 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___166_1299.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___166_1299.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___166_1299.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___166_1299.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___166_1299.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___166_1299.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___166_1299.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___166_1299.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___166_1299.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1312  ->
      match uu___6_1312 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1319  ->
    match uu___7_1319 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1332  ->
    match uu___8_1332 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1347  ->
    match uu___9_1347 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1362  ->
    match uu___10_1362 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1376  ->
    match uu___11_1376 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1390  ->
    match uu___12_1390 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1402  ->
    match uu___13_1402 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1418 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1418) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1448 =
          let uu____1450 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1450  in
        if uu____1448
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1487)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1534 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1558 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1558]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1534
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1586 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1610 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1610]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1586
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1657 =
          let uu____1659 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1659  in
        if uu____1657
        then ()
        else
          (let uu____1664 =
             let uu____1667 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1667
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1664 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1716 =
          let uu____1718 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1718  in
        if uu____1716
        then ()
        else
          (let uu____1723 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1723)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1743 =
        let uu____1745 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1745  in
      if uu____1743
      then ()
      else
        (let msgf m =
           let uu____1759 =
             let uu____1761 =
               let uu____1763 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1763 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1761  in
           Prims.op_Hat msg uu____1759  in
         (let uu____1768 = msgf "scope"  in
          let uu____1771 = p_scope prob  in
          def_scope_wf uu____1768 (p_loc prob) uu____1771);
         (let uu____1783 = msgf "guard"  in
          def_check_scoped uu____1783 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1790 = msgf "lhs"  in
                def_check_scoped uu____1790 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1793 = msgf "rhs"  in
                def_check_scoped uu____1793 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1800 = msgf "lhs"  in
                def_check_scoped_comp uu____1800 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1803 = msgf "rhs"  in
                def_check_scoped_comp uu____1803 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___259_1824 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___259_1824.wl_deferred);
          ctr = (uu___259_1824.ctr);
          defer_ok = (uu___259_1824.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___259_1824.umax_heuristic_ok);
          tcenv = (uu___259_1824.tcenv);
          wl_implicits = (uu___259_1824.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1832 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1832 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___263_1855 = empty_worklist env  in
      let uu____1856 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1856;
        wl_deferred = (uu___263_1855.wl_deferred);
        ctr = (uu___263_1855.ctr);
        defer_ok = (uu___263_1855.defer_ok);
        smt_ok = (uu___263_1855.smt_ok);
        umax_heuristic_ok = (uu___263_1855.umax_heuristic_ok);
        tcenv = (uu___263_1855.tcenv);
        wl_implicits = (uu___263_1855.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___268_1877 = wl  in
        {
          attempting = (uu___268_1877.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___268_1877.ctr);
          defer_ok = (uu___268_1877.defer_ok);
          smt_ok = (uu___268_1877.smt_ok);
          umax_heuristic_ok = (uu___268_1877.umax_heuristic_ok);
          tcenv = (uu___268_1877.tcenv);
          wl_implicits = (uu___268_1877.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1904 = FStar_Thunk.mkv reason  in defer uu____1904 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___276_1923 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___276_1923.wl_deferred);
         ctr = (uu___276_1923.ctr);
         defer_ok = (uu___276_1923.defer_ok);
         smt_ok = (uu___276_1923.smt_ok);
         umax_heuristic_ok = (uu___276_1923.umax_heuristic_ok);
         tcenv = (uu___276_1923.tcenv);
         wl_implicits = (uu___276_1923.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1937 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1937 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1971 = FStar_Syntax_Util.type_u ()  in
            match uu____1971 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1983 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1983 with
                 | (uu____2001,tt,wl1) ->
                     let uu____2004 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2004, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2010  ->
    match uu___14_2010 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2016  -> FStar_TypeChecker_Common.TProb _2016) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2022  -> FStar_TypeChecker_Common.CProb _2022) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2030 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2030 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2050  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2092 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2092 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2092 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2092 FStar_TypeChecker_Common.problem *
                      worklist)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None  -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____2179 =
                          let uu____2188 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2188]  in
                        FStar_List.append scope uu____2179
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2231 =
                      let uu____2234 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2234  in
                    FStar_List.append uu____2231
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2253 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2253 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2279 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2279;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_t.arg") orig;
                  (let uu____2353 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2353 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_c.arg") orig;
                  (let uu____2441 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2441 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2479 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2479 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2479 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2479 FStar_TypeChecker_Common.problem *
                      worklist)
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun subject  ->
              fun loc  ->
                fun reason  ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2547 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2547]  in
                        let uu____2566 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2566
                     in
                  let uu____2569 =
                    let uu____2576 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___359_2587 = wl  in
                       {
                         attempting = (uu___359_2587.attempting);
                         wl_deferred = (uu___359_2587.wl_deferred);
                         ctr = (uu___359_2587.ctr);
                         defer_ok = (uu___359_2587.defer_ok);
                         smt_ok = (uu___359_2587.smt_ok);
                         umax_heuristic_ok =
                           (uu___359_2587.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___359_2587.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2576
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2569 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2605 =
                              let uu____2606 =
                                let uu____2615 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____2615
                                 in
                              [uu____2606]  in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____2605 loc
                         in
                      let prob =
                        let uu____2643 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2643;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = subject;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = [reason];
                          FStar_TypeChecker_Common.loc = loc;
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem)
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let p =
                let uu____2691 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2691;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStar_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }  in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
  
let guard_on_element :
  'Auu____2706 .
    worklist ->
      'Auu____2706 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu____2739 =
                let uu____2742 =
                  let uu____2743 =
                    let uu____2750 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2750)  in
                  FStar_Syntax_Syntax.NT uu____2743  in
                [uu____2742]  in
              FStar_Syntax_Subst.subst uu____2739 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2772 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2772
        then
          let uu____2780 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2783 = prob_to_string env d  in
          let uu____2785 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2792 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2780 uu____2783 uu____2785 uu____2792
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2804 -> failwith "impossible"  in
           let uu____2807 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.term_to_string env)
                   tp.FStar_TypeChecker_Common.lhs
                   tp.FStar_TypeChecker_Common.rhs
             | FStar_TypeChecker_Common.CProb cp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.comp_to_string env)
                   cp.FStar_TypeChecker_Common.lhs
                   cp.FStar_TypeChecker_Common.rhs
              in
           match uu____2807 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2850  ->
            match uu___15_2850 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2862 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2866 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2866 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2897  ->
           match uu___16_2897 with
           | UNIV uu____2900 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2907 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2907
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___17_2935  ->
           match uu___17_2935 with
           | UNIV (u',t) ->
               let uu____2940 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2940
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2947 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2959 =
        let uu____2960 =
          let uu____2961 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2961
           in
        FStar_Syntax_Subst.compress uu____2960  in
      FStar_All.pipe_right uu____2959 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2973 =
        let uu____2974 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2974  in
      FStar_All.pipe_right uu____2973 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2986 =
        let uu____2990 =
          let uu____2992 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2992  in
        FStar_Pervasives_Native.Some uu____2990  in
      FStar_Profiling.profile (fun uu____2995  -> sn' env t) uu____2986
        "FStar.TypeChecker.Rel.sn"
  
let (norm_with_steps :
  Prims.string ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun profiling_tag  ->
    fun steps  ->
      fun env  ->
        fun t  ->
          let uu____3020 =
            let uu____3024 =
              let uu____3026 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3026  in
            FStar_Pervasives_Native.Some uu____3024  in
          FStar_Profiling.profile
            (fun uu____3029  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3020
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3037 = FStar_Syntax_Util.head_and_args t  in
    match uu____3037 with
    | (h,uu____3056) ->
        let uu____3081 =
          let uu____3082 = FStar_Syntax_Subst.compress h  in
          uu____3082.FStar_Syntax_Syntax.n  in
        (match uu____3081 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3087 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3100 =
        let uu____3104 =
          let uu____3106 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3106  in
        FStar_Pervasives_Native.Some uu____3104  in
      FStar_Profiling.profile
        (fun uu____3111  ->
           let uu____3112 = should_strongly_reduce t  in
           if uu____3112
           then
             let uu____3115 =
               let uu____3116 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3116  in
             FStar_All.pipe_right uu____3115 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3100 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3127 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3127) ->
        (FStar_Syntax_Syntax.term * 'Auu____3127)
  =
  fun env  ->
    fun t  ->
      let uu____3150 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3150, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____3202  ->
              match uu____3202 with
              | (x,imp) ->
                  let uu____3221 =
                    let uu___465_3222 = x  in
                    let uu____3223 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___465_3222.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___465_3222.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3223
                    }  in
                  (uu____3221, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3247 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3247
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3251 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3251
        | uu____3254 -> u2  in
      let uu____3255 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3255
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3272 =
          let uu____3276 =
            let uu____3278 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3278  in
          FStar_Pervasives_Native.Some uu____3276  in
        FStar_Profiling.profile
          (fun uu____3281  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3272 "FStar.TypeChecker.Rel.normalize_refinement"
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF]  in
          normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3403 = norm_refinement env t12  in
                 match uu____3403 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3418;
                     FStar_Syntax_Syntax.vars = uu____3419;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3443 =
                       let uu____3445 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3447 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3445 uu____3447
                        in
                     failwith uu____3443)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3463 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3463
          | FStar_Syntax_Syntax.Tm_uinst uu____3464 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3501 =
                   let uu____3502 = FStar_Syntax_Subst.compress t1'  in
                   uu____3502.FStar_Syntax_Syntax.n  in
                 match uu____3501 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3517 -> aux true t1'
                 | uu____3525 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3540 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3571 =
                   let uu____3572 = FStar_Syntax_Subst.compress t1'  in
                   uu____3572.FStar_Syntax_Syntax.n  in
                 match uu____3571 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3587 -> aux true t1'
                 | uu____3595 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3610 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3657 =
                   let uu____3658 = FStar_Syntax_Subst.compress t1'  in
                   uu____3658.FStar_Syntax_Syntax.n  in
                 match uu____3657 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3673 -> aux true t1'
                 | uu____3681 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3696 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3711 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3726 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3741 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3756 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3785 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3818 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3839 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3866 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3894 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3931 ->
              let uu____3938 =
                let uu____3940 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3942 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3940 uu____3942
                 in
              failwith uu____3938
          | FStar_Syntax_Syntax.Tm_ascribed uu____3957 ->
              let uu____3984 =
                let uu____3986 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3988 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3986 uu____3988
                 in
              failwith uu____3984
          | FStar_Syntax_Syntax.Tm_delayed uu____4003 ->
              let uu____4018 =
                let uu____4020 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4022 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4020 uu____4022
                 in
              failwith uu____4018
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4037 =
                let uu____4039 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4041 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4039 uu____4041
                 in
              failwith uu____4037
           in
        let uu____4056 = whnf env t1  in aux false uu____4056
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____4101 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4101 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4142 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4142, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4169 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4169 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4229  ->
    match uu____4229 with
    | (t_base,refopt) ->
        let uu____4260 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4260 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4302 =
      let uu____4306 =
        let uu____4309 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4334  ->
                  match uu____4334 with | (uu____4342,uu____4343,x) -> x))
           in
        FStar_List.append wl.attempting uu____4309  in
      FStar_List.map (wl_prob_to_string wl) uu____4306  in
    FStar_All.pipe_right uu____4302 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4364 .
    ('Auu____4364 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4376  ->
    match uu____4376 with
    | (uu____4383,c,args) ->
        let uu____4386 = print_ctx_uvar c  in
        let uu____4388 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4386 uu____4388
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4398 = FStar_Syntax_Util.head_and_args t  in
    match uu____4398 with
    | (head1,_args) ->
        let uu____4442 =
          let uu____4443 = FStar_Syntax_Subst.compress head1  in
          uu____4443.FStar_Syntax_Syntax.n  in
        (match uu____4442 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4447 -> true
         | uu____4461 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4469 = FStar_Syntax_Util.head_and_args t  in
    match uu____4469 with
    | (head1,_args) ->
        let uu____4512 =
          let uu____4513 = FStar_Syntax_Subst.compress head1  in
          uu____4513.FStar_Syntax_Syntax.n  in
        (match uu____4512 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4517) -> u
         | uu____4534 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4559 = FStar_Syntax_Util.head_and_args t  in
      match uu____4559 with
      | (head1,args) ->
          let uu____4606 =
            let uu____4607 = FStar_Syntax_Subst.compress head1  in
            uu____4607.FStar_Syntax_Syntax.n  in
          (match uu____4606 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4615)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4648 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4673  ->
                         match uu___18_4673 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4678 =
                               let uu____4679 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4679.FStar_Syntax_Syntax.n  in
                             (match uu____4678 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4684 -> false)
                         | uu____4686 -> true))
                  in
               (match uu____4648 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4711 =
                        FStar_List.collect
                          (fun uu___19_4723  ->
                             match uu___19_4723 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4727 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4727]
                             | uu____4728 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4711 FStar_List.rev  in
                    let uu____4751 =
                      let uu____4758 =
                        let uu____4767 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4789  ->
                                  match uu___20_4789 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4793 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4793]
                                  | uu____4794 -> []))
                           in
                        FStar_All.pipe_right uu____4767 FStar_List.rev  in
                      let uu____4817 =
                        let uu____4820 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4820  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4758 uu____4817
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4751 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4856  ->
                                match uu____4856 with
                                | (x,i) ->
                                    let uu____4875 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4875, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4904  ->
                                match uu____4904 with
                                | (a,i) ->
                                    let uu____4923 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4923, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v1, all_args), wl1))))
           | uu____4943 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4965 =
          let uu____4988 =
            let uu____4989 = FStar_Syntax_Subst.compress k  in
            uu____4989.FStar_Syntax_Syntax.n  in
          match uu____4988 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5071 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5071)
              else
                (let uu____5106 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5106 with
                 | (ys',t1,uu____5139) ->
                     let uu____5144 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5144))
          | uu____5183 ->
              let uu____5184 =
                let uu____5189 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5189)  in
              ((ys, t), uu____5184)
           in
        match uu____4965 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____5284 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5284 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let assign_solution xs uv phi1 =
               (let uu____5362 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5362
                then
                  let uu____5367 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5369 = print_ctx_uvar uv  in
                  let uu____5371 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5367 uu____5369 uu____5371
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5380 =
                   let uu____5382 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5382  in
                 let uu____5385 =
                   let uu____5388 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5388
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5380 uu____5385 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5421 =
               let uu____5422 =
                 let uu____5424 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5426 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5424 uu____5426
                  in
               failwith uu____5422  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5492  ->
                       match uu____5492 with
                       | (a,i) ->
                           let uu____5513 =
                             let uu____5514 = FStar_Syntax_Subst.compress a
                                in
                             uu____5514.FStar_Syntax_Syntax.n  in
                           (match uu____5513 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5540 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5550 =
                 let uu____5552 = is_flex g  in Prims.op_Negation uu____5552
                  in
               if uu____5550
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5561 = destruct_flex_t g wl  in
                  match uu____5561 with
                  | ((uu____5566,uv1,args),wl1) ->
                      ((let uu____5571 = args_as_binders args  in
                        assign_solution uu____5571 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___718_5573 = wl1  in
              {
                attempting = (uu___718_5573.attempting);
                wl_deferred = (uu___718_5573.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___718_5573.defer_ok);
                smt_ok = (uu___718_5573.smt_ok);
                umax_heuristic_ok = (uu___718_5573.umax_heuristic_ok);
                tcenv = (uu___718_5573.tcenv);
                wl_implicits = (uu___718_5573.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5598 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5598
         then
           let uu____5603 = FStar_Util.string_of_int pid  in
           let uu____5605 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5603 uu____5605
         else ());
        commit sol;
        (let uu___726_5611 = wl  in
         {
           attempting = (uu___726_5611.attempting);
           wl_deferred = (uu___726_5611.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___726_5611.defer_ok);
           smt_ok = (uu___726_5611.smt_ok);
           umax_heuristic_ok = (uu___726_5611.umax_heuristic_ok);
           tcenv = (uu___726_5611.tcenv);
           wl_implicits = (uu___726_5611.wl_implicits)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let uu____5647 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5647
           then
             let uu____5652 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5656 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5652 uu____5656
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____5683 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5683 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars1
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars1, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk  ->
    fun t  ->
      let uu____5723 = occurs uk t  in
      match uu____5723 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5762 =
                 let uu____5764 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5766 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5764 uu____5766
                  in
               FStar_Pervasives_Native.Some uu____5762)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders *
        FStar_Syntax_Syntax.binders)))
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____5886 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5886 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5937 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5994  ->
             match uu____5994 with
             | (x,uu____6006) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6024 = FStar_List.last bs  in
      match uu____6024 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6048) ->
          let uu____6059 =
            FStar_Util.prefix_until
              (fun uu___21_6074  ->
                 match uu___21_6074 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6077 -> false) g
             in
          (match uu____6059 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6091,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6128 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6128 with
        | (pfx,uu____6138) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6150 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6150 with
             | (uu____6158,src',wl1) ->
                 (FStar_Syntax_Unionfind.change
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
  
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt  ->
    fun sources  ->
      fun wl  -> FStar_List.fold_right (restrict_ctx tgt) sources wl
  
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g  ->
    fun v1  ->
      fun v2  ->
        let as_set1 v3 =
          FStar_All.pipe_right v3
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set1 v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6272 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6273 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6337  ->
                  fun uu____6338  ->
                    match (uu____6337, uu____6338) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6441 =
                          let uu____6443 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6443
                           in
                        if uu____6441
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6477 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6477
                           then
                             let uu____6494 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6494)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6273 with | (isect,uu____6544) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6580 'Auu____6581 .
    (FStar_Syntax_Syntax.bv * 'Auu____6580) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6581) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6639  ->
              fun uu____6640  ->
                match (uu____6639, uu____6640) with
                | ((a,uu____6659),(b,uu____6661)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6677 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6677) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6708  ->
           match uu____6708 with
           | (y,uu____6715) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6725 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6725) Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg,i)::args2 ->
              let hd1 = sn env arg  in
              (match hd1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6887 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6887
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6920 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____6972 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7016 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7037 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7045  ->
    match uu___22_7045 with
    | MisMatch (d1,d2) ->
        let uu____7057 =
          let uu____7059 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7061 =
            let uu____7063 =
              let uu____7065 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7065 ")"  in
            Prims.op_Hat ") (" uu____7063  in
          Prims.op_Hat uu____7059 uu____7061  in
        Prims.op_Hat "MisMatch (" uu____7057
    | HeadMatch u ->
        let uu____7072 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7072
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7081  ->
    match uu___23_7081 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7098 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d1
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7120 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7120 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7131 -> d)
      | d1 -> d1
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____7155 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7165 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7184 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7184
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7185 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7186 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7187 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7200 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7214 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7238) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7244,uu____7245) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7287) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7312;
             FStar_Syntax_Syntax.index = uu____7313;
             FStar_Syntax_Syntax.sort = t2;_},uu____7315)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7323 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7324 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7325 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7340 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7347 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7367 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7367
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7386;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7387;
             FStar_Syntax_Syntax.ltyp = uu____7388;
             FStar_Syntax_Syntax.rng = uu____7389;_},uu____7390)
            ->
            let uu____7401 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7401 t21
        | (uu____7402,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7403;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7404;
             FStar_Syntax_Syntax.ltyp = uu____7405;
             FStar_Syntax_Syntax.rng = uu____7406;_})
            ->
            let uu____7417 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7417
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7429 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7429
            then FullMatch
            else
              (let uu____7434 =
                 let uu____7443 =
                   let uu____7446 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7446  in
                 let uu____7447 =
                   let uu____7450 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7450  in
                 (uu____7443, uu____7447)  in
               MisMatch uu____7434)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7456),FStar_Syntax_Syntax.Tm_uinst (g,uu____7458)) ->
            let uu____7467 = head_matches env f g  in
            FStar_All.pipe_right uu____7467 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7468) -> HeadMatch true
        | (uu____7470,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7474 = FStar_Const.eq_const c d  in
            if uu____7474
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7484),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7486)) ->
            let uu____7519 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7519
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7529),FStar_Syntax_Syntax.Tm_refine (y,uu____7531)) ->
            let uu____7540 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7540 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7542),uu____7543) ->
            let uu____7548 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7548 head_match
        | (uu____7549,FStar_Syntax_Syntax.Tm_refine (x,uu____7551)) ->
            let uu____7556 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7556 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7557,FStar_Syntax_Syntax.Tm_type
           uu____7558) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7560,FStar_Syntax_Syntax.Tm_arrow uu____7561) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7592),FStar_Syntax_Syntax.Tm_app (head',uu____7594))
            ->
            let uu____7643 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7643 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7645),uu____7646) ->
            let uu____7671 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7671 head_match
        | (uu____7672,FStar_Syntax_Syntax.Tm_app (head1,uu____7674)) ->
            let uu____7699 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7699 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7700,FStar_Syntax_Syntax.Tm_let
           uu____7701) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7729,FStar_Syntax_Syntax.Tm_match uu____7730) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7776,FStar_Syntax_Syntax.Tm_abs
           uu____7777) -> HeadMatch true
        | uu____7815 ->
            let uu____7820 =
              let uu____7829 = delta_depth_of_term env t11  in
              let uu____7832 = delta_depth_of_term env t21  in
              (uu____7829, uu____7832)  in
            MisMatch uu____7820
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    worklist ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let head1 =
              let uu____7901 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7901  in
            (let uu____7903 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7903
             then
               let uu____7908 = FStar_Syntax_Print.term_to_string t  in
               let uu____7910 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7908 uu____7910
             else ());
            (let uu____7915 =
               let uu____7916 = FStar_Syntax_Util.un_uinst head1  in
               uu____7916.FStar_Syntax_Syntax.n  in
             match uu____7915 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7922 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7922 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7936 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7936
                        then
                          let uu____7941 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7941
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7946 ->
                      let basic_steps =
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota]  in
                      let steps =
                        if wl.smt_ok
                        then basic_steps
                        else
                          (FStar_TypeChecker_Env.Exclude
                             FStar_TypeChecker_Env.Zeta)
                          :: basic_steps
                         in
                      let t' =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.1" steps env
                          t
                         in
                      let uu____7964 =
                        let uu____7966 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7966 = FStar_Syntax_Util.Equal  in
                      if uu____7964
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7973 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7973
                          then
                            let uu____7978 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7980 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7978
                              uu____7980
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7985 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry1 n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8137 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8137
             then
               let uu____8142 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8144 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8146 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8142
                 uu____8144 uu____8146
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8174 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   (t1', t21)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21
                       in
                    (t11, t2'))
                  in
               match uu____8174 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8222 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8222 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21
                      in
                   aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____8260),uu____8261)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8282 =
                      let uu____8291 = maybe_inline t11  in
                      let uu____8294 = maybe_inline t21  in
                      (uu____8291, uu____8294)  in
                    match uu____8282 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu____8337,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8338))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8359 =
                      let uu____8368 = maybe_inline t11  in
                      let uu____8371 = maybe_inline t21  in
                      (uu____8368, uu____8371)  in
                    match uu____8359 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____8426 -> fail1 n_delta r t11 t21
             | uu____8435 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8450 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8450
           then
             let uu____8455 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8457 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8459 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8467 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8484 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8484
                    (fun uu____8519  ->
                       match uu____8519 with
                       | (t11,t21) ->
                           let uu____8527 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8529 =
                             let uu____8531 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8531  in
                           Prims.op_Hat uu____8527 uu____8529))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8455 uu____8457 uu____8459 uu____8467
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8548 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8548 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8563  ->
    match uu___24_8563 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.of_int (5))
  
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (rank_t_num r1) <= (rank_t_num r2) 
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2)) 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___1215_8612 = p  in
      let uu____8615 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8616 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1215_8612.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8615;
        FStar_TypeChecker_Common.relation =
          (uu___1215_8612.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8616;
        FStar_TypeChecker_Common.element =
          (uu___1215_8612.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1215_8612.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1215_8612.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1215_8612.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1215_8612.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1215_8612.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8631 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8631
            (fun _8636  -> FStar_TypeChecker_Common.TProb _8636)
      | FStar_TypeChecker_Common.CProb uu____8637 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8660 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8660 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8668 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8668 with
           | (lh,lhs_args) ->
               let uu____8715 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8715 with
                | (rh,rhs_args) ->
                    let uu____8762 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8775,FStar_Syntax_Syntax.Tm_uvar uu____8776)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8865 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8892,uu____8893)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8908,FStar_Syntax_Syntax.Tm_uvar uu____8909)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8924,FStar_Syntax_Syntax.Tm_arrow uu____8925)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8955 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8955.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8955.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8955.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8955.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8955.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8955.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8955.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8955.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8955.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8958,FStar_Syntax_Syntax.Tm_type uu____8959)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8975 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8975.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8975.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8975.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8975.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8975.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8975.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8975.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8975.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8975.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8978,FStar_Syntax_Syntax.Tm_uvar uu____8979)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8995 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8995.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8995.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8995.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8995.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8995.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8995.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8995.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8995.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8995.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8998,FStar_Syntax_Syntax.Tm_uvar uu____8999)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9014,uu____9015)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9030,FStar_Syntax_Syntax.Tm_uvar uu____9031)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9046,uu____9047) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8762 with
                     | (rank,tp1) ->
                         let uu____9060 =
                           FStar_All.pipe_right
                             (let uu___1286_9064 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1286_9064.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1286_9064.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1286_9064.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1286_9064.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1286_9064.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1286_9064.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1286_9064.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1286_9064.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1286_9064.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9067  ->
                                FStar_TypeChecker_Common.TProb _9067)
                            in
                         (rank, uu____9060))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9071 =
            FStar_All.pipe_right
              (let uu___1290_9075 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1290_9075.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1290_9075.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1290_9075.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1290_9075.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1290_9075.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1290_9075.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1290_9075.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1290_9075.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1290_9075.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9078  -> FStar_TypeChecker_Common.CProb _9078)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9071)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9138 probs =
      match uu____9138 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9219 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9240 = rank wl.tcenv hd1  in
               (match uu____9240 with
                | (rank1,hd2) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out (m :: tl1)), rank1))
                    else
                      (let uu____9301 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9306 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9306)
                          in
                       if uu____9301
                       then
                         match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), (m ::
                                 out)) tl1
                       else aux (min_rank, min1, (hd2 :: out)) tl1)))
       in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv  ->
    fun bs  ->
      fun p  ->
        let flex_will_be_closed t =
          let uu____9379 = FStar_Syntax_Util.head_and_args t  in
          match uu____9379 with
          | (hd1,uu____9398) ->
              let uu____9423 =
                let uu____9424 = FStar_Syntax_Subst.compress hd1  in
                uu____9424.FStar_Syntax_Syntax.n  in
              (match uu____9423 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9429) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9464  ->
                           match uu____9464 with
                           | (y,uu____9473) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9496  ->
                                       match uu____9496 with
                                       | (x,uu____9505) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9510 -> false)
           in
        let uu____9512 = rank tcenv p  in
        match uu____9512 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9521 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid  -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq  -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> true
                  | FStar_TypeChecker_Common.Flex_rigid  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex  ->
                      (p2.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStar_TypeChecker_Common.rhs))))
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of lstring 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9602 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9621 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9640 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9657 = FStar_Thunk.mkv s  in UFailed uu____9657 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9672 = mklstr s  in UFailed uu____9672 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____9723 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9723 with
                        | (k,uu____9731) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9744 -> false)))
            | uu____9746 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9798 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9806 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9806 = Prims.int_zero))
                           in
                        if uu____9798 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9827 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9835 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9835 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9827)
               in
            let uu____9839 = filter1 u12  in
            let uu____9842 = filter1 u22  in (uu____9839, uu____9842)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9877 = filter_out_common_univs us1 us2  in
                   (match uu____9877 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9937 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9937 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9940 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9957  ->
                               let uu____9958 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9960 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9958 uu____9960))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9986 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9986 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10012 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10012 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10015 ->
                   ufailed_thunk
                     (fun uu____10026  ->
                        let uu____10027 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10029 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10027 uu____10029 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10032,uu____10033) ->
              let uu____10035 =
                let uu____10037 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10039 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10037 uu____10039
                 in
              failwith uu____10035
          | (FStar_Syntax_Syntax.U_unknown ,uu____10042) ->
              let uu____10043 =
                let uu____10045 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10047 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10045 uu____10047
                 in
              failwith uu____10043
          | (uu____10050,FStar_Syntax_Syntax.U_bvar uu____10051) ->
              let uu____10053 =
                let uu____10055 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10057 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10055 uu____10057
                 in
              failwith uu____10053
          | (uu____10060,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10061 =
                let uu____10063 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10065 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10063 uu____10065
                 in
              failwith uu____10061
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10095 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10095
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10112 = occurs_univ v1 u3  in
              if uu____10112
              then
                let uu____10115 =
                  let uu____10117 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10119 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10117 uu____10119
                   in
                try_umax_components u11 u21 uu____10115
              else
                (let uu____10124 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10124)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10136 = occurs_univ v1 u3  in
              if uu____10136
              then
                let uu____10139 =
                  let uu____10141 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10143 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10141 uu____10143
                   in
                try_umax_components u11 u21 uu____10139
              else
                (let uu____10148 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10148)
          | (FStar_Syntax_Syntax.U_max uu____10149,uu____10150) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10158 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10158
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10164,FStar_Syntax_Syntax.U_max uu____10165) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10173 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10173
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10179,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10181,FStar_Syntax_Syntax.U_name uu____10182) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10184) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10186) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10188,FStar_Syntax_Syntax.U_succ uu____10189) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10191,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list * ('a Prims.list -> 'b)) ->
      ('a Prims.list * ('a Prims.list -> 'b)) ->
        (('a Prims.list * 'b) * ('a Prims.list * 'b))
  =
  fun bc1  ->
    fun bc2  ->
      let uu____10298 = bc1  in
      match uu____10298 with
      | (bs1,mk_cod1) ->
          let uu____10342 = bc2  in
          (match uu____10342 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10453 = aux xs ys  in
                     (match uu____10453 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10536 =
                       let uu____10543 = mk_cod1 xs  in ([], uu____10543)  in
                     let uu____10546 =
                       let uu____10553 = mk_cod2 ys  in ([], uu____10553)  in
                     (uu____10536, uu____10546)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____10622 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10622 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10625 =
                    let uu____10626 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10626 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10625
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10631 = has_type_guard t1 t2  in (uu____10631, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10632 = has_type_guard t2 t1  in (uu____10632, wl)
  
let is_flex_pat :
  'Auu____10642 'Auu____10643 'Auu____10644 .
    ('Auu____10642 * 'Auu____10643 * 'Auu____10644 Prims.list) -> Prims.bool
  =
  fun uu___25_10658  ->
    match uu___25_10658 with
    | (uu____10667,uu____10668,[]) -> true
    | uu____10672 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10705 = f  in
      match uu____10705 with
      | (uu____10712,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10713;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10714;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10717;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10718;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10719;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10720;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10790  ->
                 match uu____10790 with
                 | (y,uu____10799) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10953 =
                  let uu____10968 =
                    let uu____10971 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10971  in
                  ((FStar_List.rev pat_binders), uu____10968)  in
                FStar_Pervasives_Native.Some uu____10953
            | (uu____11004,[]) ->
                let uu____11035 =
                  let uu____11050 =
                    let uu____11053 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11053  in
                  ((FStar_List.rev pat_binders), uu____11050)  in
                FStar_Pervasives_Native.Some uu____11035
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11144 =
                  let uu____11145 = FStar_Syntax_Subst.compress a  in
                  uu____11145.FStar_Syntax_Syntax.n  in
                (match uu____11144 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11165 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11165
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1618_11195 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1618_11195.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1618_11195.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11199 =
                            let uu____11200 =
                              let uu____11207 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11207)  in
                            FStar_Syntax_Syntax.NT uu____11200  in
                          [uu____11199]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1624_11223 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1624_11223.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1624_11223.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11224 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11264 =
                  let uu____11271 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11271  in
                (match uu____11264 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11330 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11355 ->
               let uu____11356 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11356 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11652 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11652
       then
         let uu____11657 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11657
       else ());
      (let uu____11663 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11663
       then
         let uu____11668 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11668
       else ());
      (let uu____11673 = next_prob probs  in
       match uu____11673 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1651_11700 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1651_11700.wl_deferred);
               ctr = (uu___1651_11700.ctr);
               defer_ok = (uu___1651_11700.defer_ok);
               smt_ok = (uu___1651_11700.smt_ok);
               umax_heuristic_ok = (uu___1651_11700.umax_heuristic_ok);
               tcenv = (uu___1651_11700.tcenv);
               wl_implicits = (uu___1651_11700.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11709 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11709
                 then
                   let uu____11712 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11712
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       (let uu____11719 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11719)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1663_11725 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1663_11725.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1663_11725.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1663_11725.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1663_11725.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1663_11725.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1663_11725.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1663_11725.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1663_11725.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1663_11725.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11750 ->
                let uu____11760 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11825  ->
                          match uu____11825 with
                          | (c,uu____11835,uu____11836) -> c < probs.ctr))
                   in
                (match uu____11760 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11884 =
                            let uu____11889 =
                              FStar_List.map
                                (fun uu____11910  ->
                                   match uu____11910 with
                                   | (uu____11926,x,y) ->
                                       let uu____11937 = FStar_Thunk.force x
                                          in
                                       (uu____11937, y)) probs.wl_deferred
                               in
                            (uu____11889, (probs.wl_implicits))  in
                          Success uu____11884
                      | uu____11941 ->
                          let uu____11951 =
                            let uu___1681_11952 = probs  in
                            let uu____11953 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11974  ->
                                      match uu____11974 with
                                      | (uu____11982,uu____11983,y) -> y))
                               in
                            {
                              attempting = uu____11953;
                              wl_deferred = rest;
                              ctr = (uu___1681_11952.ctr);
                              defer_ok = (uu___1681_11952.defer_ok);
                              smt_ok = (uu___1681_11952.smt_ok);
                              umax_heuristic_ok =
                                (uu___1681_11952.umax_heuristic_ok);
                              tcenv = (uu___1681_11952.tcenv);
                              wl_implicits = (uu___1681_11952.wl_implicits)
                            }  in
                          solve env uu____11951))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____11992 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11992 with
            | USolved wl1 ->
                let uu____11994 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11994
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11997 = defer_lit "" orig wl1  in
                solve env uu____11997

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____12048 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12048 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12051 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12064;
                  FStar_Syntax_Syntax.vars = uu____12065;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12068;
                  FStar_Syntax_Syntax.vars = uu____12069;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12082,uu____12083) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12091,FStar_Syntax_Syntax.Tm_uinst uu____12092) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12100 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> lstring -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____12111 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12111
              then
                let uu____12116 = prob_to_string env orig  in
                let uu____12118 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12116 uu____12118
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1  ->
    fun env  ->
      fun tp  ->
        fun wl  ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____12211 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12211 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12266 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12266
                then
                  let uu____12271 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12273 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12271 uu____12273
                else ());
               (let uu____12278 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12278 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12324 = eq_prob t1 t2 wl2  in
                         (match uu____12324 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12345 ->
                         let uu____12354 = eq_prob t1 t2 wl2  in
                         (match uu____12354 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12404 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12419 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12420 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12419, uu____12420)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12425 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12426 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12425, uu____12426)
                            in
                         (match uu____12404 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12457 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12457 with
                                | (t1_hd,t1_args) ->
                                    let uu____12502 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12502 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12568 =
                                              let uu____12575 =
                                                let uu____12586 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12586 :: t1_args  in
                                              let uu____12603 =
                                                let uu____12612 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12612 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12661  ->
                                                   fun uu____12662  ->
                                                     fun uu____12663  ->
                                                       match (uu____12661,
                                                               uu____12662,
                                                               uu____12663)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12713),
                                                          (a2,uu____12715))
                                                           ->
                                                           let uu____12752 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12752
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12575
                                                uu____12603
                                               in
                                            match uu____12568 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1835_12778 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1835_12778.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1835_12778.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1835_12778.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12789 =
                                                  solve env1 wl'  in
                                                (match uu____12789 with
                                                 | Success (uu____12792,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1844_12796
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1844_12796.attempting);
                                                            wl_deferred =
                                                              (uu___1844_12796.wl_deferred);
                                                            ctr =
                                                              (uu___1844_12796.ctr);
                                                            defer_ok =
                                                              (uu___1844_12796.defer_ok);
                                                            smt_ok =
                                                              (uu___1844_12796.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1844_12796.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1844_12796.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12797 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12829 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12829 with
                                | (t1_base,p1_opt) ->
                                    let uu____12865 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12865 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12964 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12964
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t
                                              in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi1),FStar_Pervasives_Native.Some
                                              (y,phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____13017 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13017
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13049 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13049
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13081 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13081
                                           | uu____13084 -> t_base  in
                                         let uu____13101 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13101 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13115 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13115, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13122 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13122 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13158 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13158 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13194 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13194
                                                         with
                                                         | (p,wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1
                                                                in
                                                             (t, [p], wl4))))))
                                 in
                              let uu____13218 = combine t11 t21 wl2  in
                              (match uu____13218 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13251 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13251
                                     then
                                       let uu____13256 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13256
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13298 ts1 =
               match uu____13298 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13361 = pairwise out t wl2  in
                        (match uu____13361 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13397 =
               let uu____13408 = FStar_List.hd ts  in (uu____13408, [], wl1)
                in
             let uu____13417 = FStar_List.tl ts  in
             aux uu____13397 uu____13417  in
           let uu____13424 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13424 with
           | (this_flex,this_rigid) ->
               let uu____13450 =
                 let uu____13451 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13451.FStar_Syntax_Syntax.n  in
               (match uu____13450 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13476 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13476
                    then
                      let uu____13479 = destruct_flex_t this_flex wl  in
                      (match uu____13479 with
                       | (flex,wl1) ->
                           let uu____13486 = quasi_pattern env flex  in
                           (match uu____13486 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13505 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13505
                                  then
                                    let uu____13510 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13510
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13517 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1946_13520 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1946_13520.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1946_13520.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1946_13520.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1946_13520.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1946_13520.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1946_13520.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1946_13520.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1946_13520.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1946_13520.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13517)
                | uu____13521 ->
                    ((let uu____13523 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13523
                      then
                        let uu____13528 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13528
                      else ());
                     (let uu____13533 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13533 with
                      | (u,_args) ->
                          let uu____13576 =
                            let uu____13577 = FStar_Syntax_Subst.compress u
                               in
                            uu____13577.FStar_Syntax_Syntax.n  in
                          (match uu____13576 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13605 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13605 with
                                 | (u',uu____13624) ->
                                     let uu____13649 =
                                       let uu____13650 = whnf env u'  in
                                       uu____13650.FStar_Syntax_Syntax.n  in
                                     (match uu____13649 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13672 -> false)
                                  in
                               let uu____13674 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13697  ->
                                         match uu___26_13697 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____13711 -> false)
                                         | uu____13715 -> false))
                                  in
                               (match uu____13674 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13730 = whnf env this_rigid
                                         in
                                      let uu____13731 =
                                        FStar_List.collect
                                          (fun uu___27_13737  ->
                                             match uu___27_13737 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13743 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13743]
                                             | uu____13747 -> [])
                                          bounds_probs
                                         in
                                      uu____13730 :: uu____13731  in
                                    let uu____13748 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13748 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13781 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13796 =
                                               let uu____13797 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13797.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13796 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13809 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13809)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13820 -> bound  in
                                           let uu____13821 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13821)  in
                                         (match uu____13781 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13856 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13856
                                                then
                                                  let wl'1 =
                                                    let uu___2006_13862 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2006_13862.wl_deferred);
                                                      ctr =
                                                        (uu___2006_13862.ctr);
                                                      defer_ok =
                                                        (uu___2006_13862.defer_ok);
                                                      smt_ok =
                                                        (uu___2006_13862.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2006_13862.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2006_13862.tcenv);
                                                      wl_implicits =
                                                        (uu___2006_13862.wl_implicits)
                                                    }  in
                                                  let uu____13863 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13863
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13869 =
                                                  solve_t env eq_prob
                                                    (let uu___2011_13871 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2011_13871.wl_deferred);
                                                       ctr =
                                                         (uu___2011_13871.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2011_13871.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2011_13871.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2011_13871.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13869 with
                                                | Success (uu____13873,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2017_13876 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2017_13876.wl_deferred);
                                                        ctr =
                                                          (uu___2017_13876.ctr);
                                                        defer_ok =
                                                          (uu___2017_13876.defer_ok);
                                                        smt_ok =
                                                          (uu___2017_13876.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2017_13876.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2017_13876.tcenv);
                                                        wl_implicits =
                                                          (uu___2017_13876.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2020_13878 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2020_13878.attempting);
                                                        wl_deferred =
                                                          (uu___2020_13878.wl_deferred);
                                                        ctr =
                                                          (uu___2020_13878.ctr);
                                                        defer_ok =
                                                          (uu___2020_13878.defer_ok);
                                                        smt_ok =
                                                          (uu___2020_13878.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2020_13878.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2020_13878.tcenv);
                                                        wl_implicits =
                                                          (FStar_List.append
                                                             wl'.wl_implicits
                                                             imps)
                                                      }  in
                                                    let g =
                                                      FStar_List.fold_left
                                                        (fun g  ->
                                                           fun p  ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs
                                                       in
                                                    let wl4 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl3
                                                       in
                                                    let uu____13894 =
                                                      FStar_List.fold_left
                                                        (fun wl5  ->
                                                           fun p  ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl5) wl4
                                                        bounds_probs
                                                       in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl4)
                                                | Failed (p,msg) ->
                                                    ((let uu____13906 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13906
                                                      then
                                                        let uu____13911 =
                                                          let uu____13913 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13913
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13911
                                                      else ());
                                                     (let uu____13926 =
                                                        let uu____13941 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13941)
                                                         in
                                                      match uu____13926 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13963))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13989 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13989
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join3"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let wl3 =
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                    [] wl2
                                                                     in
                                                                  let uu____14009
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14009))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14034 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14034
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi  in
                                                                  let wl3 =
                                                                    let uu____14054
                                                                    =
                                                                    let uu____14059
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14059
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14054
                                                                    [] wl2
                                                                     in
                                                                  let uu____14065
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14065))))
                                                      | uu____14066 ->
                                                          let uu____14081 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14081 p)))))))
                           | uu____14088 when flip ->
                               let uu____14089 =
                                 let uu____14091 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14093 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14091 uu____14093
                                  in
                               failwith uu____14089
                           | uu____14096 ->
                               let uu____14097 =
                                 let uu____14099 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14101 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14099 uu____14101
                                  in
                               failwith uu____14097)))))

and (imitate_arrow :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        flex_t ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.rel ->
                FStar_Syntax_Syntax.term -> solution)
  =
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun lhs  ->
          fun bs_lhs  ->
            fun t_res_lhs  ->
              fun rel  ->
                fun arrow1  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____14137  ->
                         match uu____14137 with
                         | (x,i) ->
                             let uu____14156 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14156, i)) bs_lhs
                     in
                  let uu____14159 = lhs  in
                  match uu____14159 with
                  | (uu____14160,u_lhs,uu____14162) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14259 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14269 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14269, univ)
                             in
                          match uu____14259 with
                          | (k,univ) ->
                              let uu____14276 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14276 with
                               | (uu____14293,u,wl3) ->
                                   let uu____14296 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14296, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14322 =
                              let uu____14335 =
                                let uu____14346 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14346 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14397  ->
                                   fun uu____14398  ->
                                     match (uu____14397, uu____14398) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14499 =
                                           let uu____14506 =
                                             let uu____14509 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14509
                                              in
                                           copy_uvar u_lhs [] uu____14506 wl2
                                            in
                                         (match uu____14499 with
                                          | (uu____14538,t_a,wl3) ->
                                              let uu____14541 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14541 with
                                               | (uu____14560,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14335
                                ([], wl1)
                               in
                            (match uu____14322 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2131_14616 = ct  in
                                   let uu____14617 =
                                     let uu____14620 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14620
                                      in
                                   let uu____14635 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2131_14616.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2131_14616.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14617;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14635;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2131_14616.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2134_14653 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2134_14653.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2134_14653.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14656 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14656 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14694 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14694 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14705 =
                                          let uu____14710 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14710)  in
                                        TERM uu____14705  in
                                      let uu____14711 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14711 with
                                       | (sub_prob,wl3) ->
                                           let uu____14725 =
                                             let uu____14726 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14726
                                              in
                                           solve env uu____14725))
                             | (x,imp)::formals2 ->
                                 let uu____14748 =
                                   let uu____14755 =
                                     let uu____14758 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14758
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14755 wl1
                                    in
                                 (match uu____14748 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14779 =
                                          let uu____14782 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14782
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14779 u_x
                                         in
                                      let uu____14783 =
                                        let uu____14786 =
                                          let uu____14789 =
                                            let uu____14790 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14790, imp)  in
                                          [uu____14789]  in
                                        FStar_List.append bs_terms
                                          uu____14786
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14783 formals2 wl2)
                              in
                           let uu____14817 = occurs_check u_lhs arrow1  in
                           (match uu____14817 with
                            | (uu____14830,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14846 =
                                    mklstr
                                      (fun uu____14851  ->
                                         let uu____14852 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14852)
                                     in
                                  giveup_or_defer env orig wl uu____14846
                                else aux [] [] formals wl))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (worklist ->
               FStar_Syntax_Syntax.binders ->
                 FStar_TypeChecker_Env.env ->
                   FStar_Syntax_Syntax.subst_elt Prims.list ->
                     (FStar_TypeChecker_Common.prob * worklist))
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____14885 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14885
               then
                 let uu____14890 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14893 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14890 (rel_to_string (p_rel orig)) uu____14893
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15024 = rhs wl1 scope env1 subst1  in
                     (match uu____15024 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15047 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15047
                            then
                              let uu____15052 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15052
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15130 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15130 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2204_15132 = hd1  in
                       let uu____15133 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2204_15132.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2204_15132.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15133
                       }  in
                     let hd21 =
                       let uu___2207_15137 = hd2  in
                       let uu____15138 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2207_15137.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2207_15137.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15138
                       }  in
                     let uu____15141 =
                       let uu____15146 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15146
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15141 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15169 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15169
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15176 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15176 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15248 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15248
                                  in
                               ((let uu____15266 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15266
                                 then
                                   let uu____15271 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15273 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15271
                                     uu____15273
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15308 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15344 = aux wl [] env [] bs1 bs2  in
               match uu____15344 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15403 = attempt sub_probs wl2  in
                   solve env1 uu____15403)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist -> (FStar_TypeChecker_Common.prob * lstring) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2245_15423 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2245_15423.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2245_15423.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15435 = try_solve env wl'  in
          match uu____15435 with
          | Success (uu____15436,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2254_15440 = wl  in
                  {
                    attempting = (uu___2254_15440.attempting);
                    wl_deferred = (uu___2254_15440.wl_deferred);
                    ctr = (uu___2254_15440.ctr);
                    defer_ok = (uu___2254_15440.defer_ok);
                    smt_ok = (uu___2254_15440.smt_ok);
                    umax_heuristic_ok = (uu___2254_15440.umax_heuristic_ok);
                    tcenv = (uu___2254_15440.tcenv);
                    wl_implicits = (FStar_List.append wl.wl_implicits imps)
                  }  in
                solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____15449 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15449 wl)

and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            let binders_as_bv_set bs =
              let uu____15463 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15463 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15497 = lhs1  in
              match uu____15497 with
              | (uu____15500,ctx_u,uu____15502) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15510 ->
                        let uu____15511 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15511 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15560 = quasi_pattern env1 lhs1  in
              match uu____15560 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15594) ->
                  let uu____15599 = lhs1  in
                  (match uu____15599 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15614 = occurs_check ctx_u rhs1  in
                       (match uu____15614 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15665 =
                                let uu____15673 =
                                  let uu____15675 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15675
                                   in
                                FStar_Util.Inl uu____15673  in
                              (uu____15665, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15703 =
                                 let uu____15705 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15705  in
                               if uu____15703
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15732 =
                                    let uu____15740 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15740  in
                                  let uu____15746 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15732, uu____15746)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15790 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15790 with
              | (rhs_hd,args) ->
                  let uu____15833 = FStar_Util.prefix args  in
                  (match uu____15833 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15903 = lhs1  in
                       (match uu____15903 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15907 =
                              let uu____15918 =
                                let uu____15925 =
                                  let uu____15928 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15928
                                   in
                                copy_uvar u_lhs [] uu____15925 wl1  in
                              match uu____15918 with
                              | (uu____15955,t_last_arg,wl2) ->
                                  let uu____15958 =
                                    let uu____15965 =
                                      let uu____15966 =
                                        let uu____15975 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15975]  in
                                      FStar_List.append bs_lhs uu____15966
                                       in
                                    copy_uvar u_lhs uu____15965 t_res_lhs wl2
                                     in
                                  (match uu____15958 with
                                   | (uu____16010,lhs',wl3) ->
                                       let uu____16013 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16013 with
                                        | (uu____16030,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15907 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16051 =
                                     let uu____16052 =
                                       let uu____16057 =
                                         let uu____16058 =
                                           let uu____16061 =
                                             let uu____16062 =
                                               FStar_Syntax_Syntax.as_arg
                                                 lhs'_last_arg
                                                in
                                             [uu____16062]  in
                                           FStar_Syntax_Syntax.mk_Tm_app lhs'
                                             uu____16061
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16058
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16057)  in
                                     TERM uu____16052  in
                                   [uu____16051]  in
                                 let uu____16087 =
                                   let uu____16094 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16094 with
                                   | (p1,wl3) ->
                                       let uu____16114 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16114 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16087 with
                                  | (sub_probs,wl3) ->
                                      let uu____16146 =
                                        let uu____16147 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16147  in
                                      solve env1 uu____16146))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16181 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16181 with
                | (uu____16199,args) ->
                    (match args with | [] -> false | uu____16235 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16254 =
                  let uu____16255 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16255.FStar_Syntax_Syntax.n  in
                match uu____16254 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16259 -> true
                | uu____16275 -> false  in
              let uu____16277 = quasi_pattern env1 lhs1  in
              match uu____16277 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16296  ->
                         let uu____16297 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16297)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16306 = is_app rhs1  in
                  if uu____16306
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16311 = is_arrow rhs1  in
                     if uu____16311
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16324  ->
                               let uu____16325 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16325)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16329 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16329
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16335 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16335
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16340 = lhs  in
                (match uu____16340 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16344 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16344 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16362 =
                              let uu____16366 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16366
                               in
                            FStar_All.pipe_right uu____16362
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16387 = occurs_check ctx_uv rhs1  in
                          (match uu____16387 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16416 =
                                   let uu____16417 =
                                     let uu____16419 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16419
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16417
                                    in
                                 giveup_or_defer env orig wl uu____16416
                               else
                                 (let uu____16427 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16427
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16434 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16434
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16450  ->
                                              let uu____16451 =
                                                names_to_string1 fvs2  in
                                              let uu____16453 =
                                                names_to_string1 fvs1  in
                                              let uu____16455 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16451 uu____16453
                                                uu____16455)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16467 ->
                          if wl.defer_ok
                          then
                            let uu____16471 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16471
                          else
                            (let uu____16476 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16476 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16502 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16502
                             | (FStar_Util.Inl msg,uu____16504) ->
                                 first_order orig env wl lhs rhs)))

and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16522 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16522
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16528 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16528
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16550 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16550
                else
                  (let uu____16555 =
                     let uu____16572 = quasi_pattern env lhs  in
                     let uu____16579 = quasi_pattern env rhs  in
                     (uu____16572, uu____16579)  in
                   match uu____16555 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16622 = lhs  in
                       (match uu____16622 with
                        | ({ FStar_Syntax_Syntax.n = uu____16623;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16625;_},u_lhs,uu____16627)
                            ->
                            let uu____16630 = rhs  in
                            (match uu____16630 with
                             | (uu____16631,u_rhs,uu____16633) ->
                                 let uu____16634 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16634
                                 then
                                   let uu____16641 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16641
                                 else
                                   (let uu____16644 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16644 with
                                    | (ctx_w,(ctx_l,ctx_r)) ->
                                        let gamma_w =
                                          gamma_until
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                            ctx_w
                                           in
                                        let zs =
                                          intersect_binders gamma_w
                                            (FStar_List.append ctx_l
                                               binders_lhs)
                                            (FStar_List.append ctx_r
                                               binders_rhs)
                                           in
                                        let uu____16676 =
                                          let uu____16683 =
                                            let uu____16686 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16686
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16683
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16676 with
                                         | (uu____16698,w,wl1) ->
                                             let w_app =
                                               let uu____16702 =
                                                 FStar_List.map
                                                   (fun uu____16713  ->
                                                      match uu____16713 with
                                                      | (z,uu____16721) ->
                                                          let uu____16726 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              z
                                                             in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu____16726) zs
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 w uu____16702
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16728 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16728
                                               then
                                                 let uu____16733 =
                                                   let uu____16737 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16739 =
                                                     let uu____16743 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16745 =
                                                       let uu____16749 =
                                                         term_to_string w  in
                                                       let uu____16751 =
                                                         let uu____16755 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16764 =
                                                           let uu____16768 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16777 =
                                                             let uu____16781
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16781]
                                                              in
                                                           uu____16768 ::
                                                             uu____16777
                                                            in
                                                         uu____16755 ::
                                                           uu____16764
                                                          in
                                                       uu____16749 ::
                                                         uu____16751
                                                        in
                                                     uu____16743 ::
                                                       uu____16745
                                                      in
                                                   uu____16737 :: uu____16739
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16733
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16798 =
                                                     let uu____16803 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16803)  in
                                                   TERM uu____16798  in
                                                 let uu____16804 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16804
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16812 =
                                                        let uu____16817 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16817)
                                                         in
                                                      TERM uu____16812  in
                                                    [s1; s2])
                                                  in
                                               let uu____16818 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16818))))))
                   | uu____16819 ->
                       let uu____16836 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16836)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16890 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16890
            then
              let uu____16895 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16897 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16899 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16901 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16895 uu____16897 uu____16899 uu____16901
            else ());
           (let uu____16912 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16912 with
            | (head1,args1) ->
                let uu____16955 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16955 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17025 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17025 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17030 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17030)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17051 =
                         mklstr
                           (fun uu____17062  ->
                              let uu____17063 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17065 = args_to_string args1  in
                              let uu____17069 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17071 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17063 uu____17065 uu____17069
                                uu____17071)
                          in
                       giveup env1 uu____17051 orig
                     else
                       (let uu____17078 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17083 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17083 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17078
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2510_17087 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2510_17087.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2510_17087.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2510_17087.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2510_17087.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2510_17087.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2510_17087.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2510_17087.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2510_17087.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17097 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17097
                                    else solve env1 wl2))
                        else
                          (let uu____17102 = base_and_refinement env1 t1  in
                           match uu____17102 with
                           | (base1,refinement1) ->
                               let uu____17127 = base_and_refinement env1 t2
                                  in
                               (match uu____17127 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let mk_sub_probs wl2 =
                                           let argp =
                                             if need_unif
                                             then
                                               FStar_List.zip
                                                 ((head1,
                                                    FStar_Pervasives_Native.None)
                                                 :: args1)
                                                 ((head2,
                                                    FStar_Pervasives_Native.None)
                                                 :: args2)
                                             else FStar_List.zip args1 args2
                                              in
                                           let uu____17292 =
                                             FStar_List.fold_right
                                               (fun uu____17332  ->
                                                  fun uu____17333  ->
                                                    match (uu____17332,
                                                            uu____17333)
                                                    with
                                                    | (((a1,uu____17385),
                                                        (a2,uu____17387)),
                                                       (probs,wl3)) ->
                                                        let uu____17436 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17436
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17292 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17479 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17479
                                                 then
                                                   let uu____17484 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17484
                                                 else ());
                                                (let uu____17490 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17490
                                                 then
                                                   FStar_List.iter
                                                     (def_check_prob
                                                        "solve_t' subprobs")
                                                     subprobs
                                                 else ());
                                                (subprobs, wl3))
                                            in
                                         let solve_sub_probs env2 wl2 =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  if Prims.op_Negation ok
                                                  then solve env2 wl3
                                                  else
                                                    (let uu____17517 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17517 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17533 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17533
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17541 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17541))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17566 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17566 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17582 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17582
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17590 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17590)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17618 =
                                           match uu____17618 with
                                           | (prob,reason) ->
                                               ((let uu____17635 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17635
                                                 then
                                                   let uu____17640 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17642 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17640 uu____17642
                                                 else ());
                                                (let uu____17648 =
                                                   let uu____17657 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17660 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17657, uu____17660)
                                                    in
                                                 match uu____17648 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17673 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17673 with
                                                      | (head1',uu____17691)
                                                          ->
                                                          let uu____17716 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17716
                                                           with
                                                           | (head2',uu____17734)
                                                               ->
                                                               let uu____17759
                                                                 =
                                                                 let uu____17764
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17765
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17764,
                                                                   uu____17765)
                                                                  in
                                                               (match uu____17759
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17767
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17767
                                                                    then
                                                                    let uu____17772
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17774
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17776
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17778
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17772
                                                                    uu____17774
                                                                    uu____17776
                                                                    uu____17778
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17783
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2598_17791
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2598_17791.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17793
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17793
                                                                    then
                                                                    let uu____17798
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17798
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17803 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17815 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17815 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17823 =
                                             let uu____17824 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17824.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17823 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17829 -> false  in
                                         (match d with
                                          | FStar_Pervasives_Native.Some d1
                                              when
                                              wl1.smt_ok &&
                                                (Prims.op_Negation
                                                   treat_as_injective)
                                              ->
                                              try_solve_without_smt_or_else
                                                env1 wl1
                                                solve_sub_probs_no_smt
                                                (unfold_and_retry d1)
                                          | uu____17832 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17835 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2618_17871 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2618_17871.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2618_17871.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2618_17871.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2618_17871.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2618_17871.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2618_17871.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2618_17871.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2618_17871.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17947 = destruct_flex_t scrutinee wl1  in
             match uu____17947 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17958 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17958 with
                  | (xs,pat_term,uu____17974,uu____17975) ->
                      let uu____17980 =
                        FStar_List.fold_left
                          (fun uu____18003  ->
                             fun x  ->
                               match uu____18003 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18024 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18024 with
                                    | (uu____18043,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17980 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18064 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18064 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2658_18081 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2658_18081.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2658_18081.umax_heuristic_ok);
                                    tcenv = (uu___2658_18081.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18092 = solve env1 wl'  in
                                (match uu____18092 with
                                 | Success (uu____18095,imps) ->
                                     let wl'1 =
                                       let uu___2666_18098 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2666_18098.wl_deferred);
                                         ctr = (uu___2666_18098.ctr);
                                         defer_ok =
                                           (uu___2666_18098.defer_ok);
                                         smt_ok = (uu___2666_18098.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2666_18098.umax_heuristic_ok);
                                         tcenv = (uu___2666_18098.tcenv);
                                         wl_implicits =
                                           (uu___2666_18098.wl_implicits)
                                       }  in
                                     let uu____18099 = solve env1 wl'1  in
                                     (match uu____18099 with
                                      | Success (uu____18102,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2674_18106 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2674_18106.attempting);
                                                 wl_deferred =
                                                   (uu___2674_18106.wl_deferred);
                                                 ctr = (uu___2674_18106.ctr);
                                                 defer_ok =
                                                   (uu___2674_18106.defer_ok);
                                                 smt_ok =
                                                   (uu___2674_18106.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2674_18106.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2674_18106.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18107 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18113 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18136 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18136
                 then
                   let uu____18141 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18143 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18141 uu____18143
                 else ());
                (let uu____18148 =
                   let uu____18169 =
                     let uu____18178 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18178)  in
                   let uu____18185 =
                     let uu____18194 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18194)  in
                   (uu____18169, uu____18185)  in
                 match uu____18148 with
                 | ((uu____18224,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18227;
                                   FStar_Syntax_Syntax.vars = uu____18228;_}),
                    (s,t)) ->
                     let uu____18299 =
                       let uu____18301 = is_flex scrutinee  in
                       Prims.op_Negation uu____18301  in
                     if uu____18299
                     then
                       ((let uu____18312 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18312
                         then
                           let uu____18317 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18317
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18336 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18336
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18351 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18351
                           then
                             let uu____18356 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18358 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18356 uu____18358
                           else ());
                          (let pat_discriminates uu___28_18383 =
                             match uu___28_18383 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18399;
                                  FStar_Syntax_Syntax.p = uu____18400;_},FStar_Pervasives_Native.None
                                ,uu____18401) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18415;
                                  FStar_Syntax_Syntax.p = uu____18416;_},FStar_Pervasives_Native.None
                                ,uu____18417) -> true
                             | uu____18444 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18547 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18547 with
                                       | (uu____18549,uu____18550,t') ->
                                           let uu____18568 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18568 with
                                            | (FullMatch ,uu____18580) ->
                                                true
                                            | (HeadMatch
                                               uu____18594,uu____18595) ->
                                                true
                                            | uu____18610 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18647 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18647
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18658 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18658 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18746,uu____18747) ->
                                       branches1
                                   | uu____18892 -> branches  in
                                 let uu____18947 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18956 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18956 with
                                        | (p,uu____18960,uu____18961) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _18990  -> FStar_Util.Inr _18990)
                                   uu____18947))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19020 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19020 with
                                | (p,uu____19029,e) ->
                                    ((let uu____19048 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19048
                                      then
                                        let uu____19053 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19055 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19053 uu____19055
                                      else ());
                                     (let uu____19060 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19075  -> FStar_Util.Inr _19075)
                                        uu____19060)))))
                 | ((s,t),(uu____19078,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19081;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19082;_}))
                     ->
                     let uu____19151 =
                       let uu____19153 = is_flex scrutinee  in
                       Prims.op_Negation uu____19153  in
                     if uu____19151
                     then
                       ((let uu____19164 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19164
                         then
                           let uu____19169 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19169
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19188 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19188
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19203 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19203
                           then
                             let uu____19208 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19210 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19208 uu____19210
                           else ());
                          (let pat_discriminates uu___28_19235 =
                             match uu___28_19235 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19251;
                                  FStar_Syntax_Syntax.p = uu____19252;_},FStar_Pervasives_Native.None
                                ,uu____19253) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19267;
                                  FStar_Syntax_Syntax.p = uu____19268;_},FStar_Pervasives_Native.None
                                ,uu____19269) -> true
                             | uu____19296 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19399 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19399 with
                                       | (uu____19401,uu____19402,t') ->
                                           let uu____19420 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19420 with
                                            | (FullMatch ,uu____19432) ->
                                                true
                                            | (HeadMatch
                                               uu____19446,uu____19447) ->
                                                true
                                            | uu____19462 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19499 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19499
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19510 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19510 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19598,uu____19599) ->
                                       branches1
                                   | uu____19744 -> branches  in
                                 let uu____19799 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19808 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19808 with
                                        | (p,uu____19812,uu____19813) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19842  -> FStar_Util.Inr _19842)
                                   uu____19799))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19872 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19872 with
                                | (p,uu____19881,e) ->
                                    ((let uu____19900 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19900
                                      then
                                        let uu____19905 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19907 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19905 uu____19907
                                      else ());
                                     (let uu____19912 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19927  -> FStar_Util.Inr _19927)
                                        uu____19912)))))
                 | uu____19928 ->
                     ((let uu____19950 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19950
                       then
                         let uu____19955 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19957 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19955 uu____19957
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20003 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20003
            then
              let uu____20008 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20010 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20012 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20014 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20008 uu____20010 uu____20012 uu____20014
            else ());
           (let uu____20019 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20019 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20050,uu____20051) ->
                     let rec may_relate head3 =
                       let uu____20079 =
                         let uu____20080 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20080.FStar_Syntax_Syntax.n  in
                       match uu____20079 with
                       | FStar_Syntax_Syntax.Tm_name uu____20084 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20086 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20111 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20111 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20113 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20116
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20117 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20120,uu____20121) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20163) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20169) ->
                           may_relate t
                       | uu____20174 -> false  in
                     let uu____20176 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20176 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20189 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20189
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20199 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20199
                          then
                            let uu____20202 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20202 with
                             | (guard,wl2) ->
                                 let uu____20209 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20209)
                          else
                            (let uu____20212 =
                               mklstr
                                 (fun uu____20223  ->
                                    let uu____20224 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20226 =
                                      let uu____20228 =
                                        let uu____20232 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20232
                                          (fun x  ->
                                             let uu____20239 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20239)
                                         in
                                      FStar_Util.dflt "" uu____20228  in
                                    let uu____20244 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20246 =
                                      let uu____20248 =
                                        let uu____20252 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20252
                                          (fun x  ->
                                             let uu____20259 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20259)
                                         in
                                      FStar_Util.dflt "" uu____20248  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20224 uu____20226 uu____20244
                                      uu____20246)
                                in
                             giveup env1 uu____20212 orig))
                 | (HeadMatch (true ),uu____20265) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20280 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20280 with
                        | (guard,wl2) ->
                            let uu____20287 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20287)
                     else
                       (let uu____20290 =
                          mklstr
                            (fun uu____20297  ->
                               let uu____20298 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20300 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20298 uu____20300)
                           in
                        giveup env1 uu____20290 orig)
                 | (uu____20303,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2849_20317 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2849_20317.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2849_20317.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2849_20317.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2849_20317.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2849_20317.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2849_20317.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2849_20317.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2849_20317.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20344 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20344
          then
            let uu____20347 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20347
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20353 =
                let uu____20356 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20356  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20353 t1);
             (let uu____20375 =
                let uu____20378 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20378  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20375 t2);
             (let uu____20397 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20397
              then
                let uu____20401 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20403 =
                  let uu____20405 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20407 =
                    let uu____20409 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20409  in
                  Prims.op_Hat uu____20405 uu____20407  in
                let uu____20412 =
                  let uu____20414 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20416 =
                    let uu____20418 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20418  in
                  Prims.op_Hat uu____20414 uu____20416  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20401 uu____20403 uu____20412
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20425,uu____20426) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20442,FStar_Syntax_Syntax.Tm_delayed uu____20443) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20459,uu____20460) ->
                  let uu____20487 =
                    let uu___2880_20488 = problem  in
                    let uu____20489 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2880_20488.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20489;
                      FStar_TypeChecker_Common.relation =
                        (uu___2880_20488.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2880_20488.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2880_20488.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2880_20488.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2880_20488.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2880_20488.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2880_20488.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2880_20488.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20487 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20490,uu____20491) ->
                  let uu____20498 =
                    let uu___2886_20499 = problem  in
                    let uu____20500 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2886_20499.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20500;
                      FStar_TypeChecker_Common.relation =
                        (uu___2886_20499.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2886_20499.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2886_20499.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2886_20499.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2886_20499.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2886_20499.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2886_20499.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2886_20499.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20498 wl
              | (uu____20501,FStar_Syntax_Syntax.Tm_ascribed uu____20502) ->
                  let uu____20529 =
                    let uu___2892_20530 = problem  in
                    let uu____20531 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2892_20530.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2892_20530.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2892_20530.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20531;
                      FStar_TypeChecker_Common.element =
                        (uu___2892_20530.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2892_20530.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2892_20530.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2892_20530.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2892_20530.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2892_20530.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20529 wl
              | (uu____20532,FStar_Syntax_Syntax.Tm_meta uu____20533) ->
                  let uu____20540 =
                    let uu___2898_20541 = problem  in
                    let uu____20542 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2898_20541.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2898_20541.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2898_20541.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20542;
                      FStar_TypeChecker_Common.element =
                        (uu___2898_20541.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2898_20541.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2898_20541.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2898_20541.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2898_20541.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2898_20541.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20540 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20544),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20546)) ->
                  let uu____20555 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20555
              | (FStar_Syntax_Syntax.Tm_bvar uu____20556,uu____20557) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20559,FStar_Syntax_Syntax.Tm_bvar uu____20560) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20630 =
                    match uu___29_20630 with
                    | [] -> c
                    | bs ->
                        let uu____20658 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20658
                     in
                  let uu____20669 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20669 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst1 c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst1 c21
                                     in
                                  let rel =
                                    let uu____20818 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20818
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation
                                     in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___30_20907 =
                    match uu___30_20907 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20949 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20949 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21094 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21095 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21094
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21095 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21097,uu____21098) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21129 -> true
                    | uu____21149 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____21209 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21217 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21217.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21217.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21217.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21217.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21217.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21217.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21217.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21217.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21217.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21217.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21217.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21217.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21217.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21217.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21217.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21217.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21217.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21217.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21217.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21217.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21217.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21217.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21217.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21217.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21217.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21217.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21217.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21217.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21217.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21217.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21217.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21217.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21217.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21217.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21217.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21217.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21217.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21217.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21217.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21217.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21217.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21217.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21217.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21217.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21209 with
                       | (uu____21222,ty,uu____21224) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21233 =
                                 let uu____21234 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21234.FStar_Syntax_Syntax.n  in
                               match uu____21233 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21237 ->
                                   let uu____21244 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21244
                               | uu____21245 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21248 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21248
                             then
                               let uu____21253 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21255 =
                                 let uu____21257 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21257
                                  in
                               let uu____21258 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21253 uu____21255 uu____21258
                             else ());
                            r1))
                     in
                  let uu____21263 =
                    let uu____21280 = maybe_eta t1  in
                    let uu____21287 = maybe_eta t2  in
                    (uu____21280, uu____21287)  in
                  (match uu____21263 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21329 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21329.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21329.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21329.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21329.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21329.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21329.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21329.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21329.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21350 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21350
                       then
                         let uu____21353 = destruct_flex_t not_abs wl  in
                         (match uu____21353 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21370 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21370.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21370.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21370.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21370.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21370.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21370.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21370.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21370.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21373 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21373 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21396 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21396
                       then
                         let uu____21399 = destruct_flex_t not_abs wl  in
                         (match uu____21399 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21416 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21416.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21416.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21416.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21416.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21416.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21416.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21416.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21416.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21419 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21419 orig))
                   | uu____21422 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21440,FStar_Syntax_Syntax.Tm_abs uu____21441) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21472 -> true
                    | uu____21492 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____21552 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21560 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21560.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21560.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21560.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21560.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21560.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21560.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21560.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21560.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21560.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21560.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21560.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21560.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21560.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21560.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21560.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21560.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21560.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21560.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21560.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21560.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21560.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21560.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21560.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21560.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21560.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21560.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21560.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21560.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21560.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21560.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21560.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21560.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21560.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21560.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21560.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21560.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21560.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21560.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21560.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21560.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21560.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21560.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21560.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21560.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21552 with
                       | (uu____21565,ty,uu____21567) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21576 =
                                 let uu____21577 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21577.FStar_Syntax_Syntax.n  in
                               match uu____21576 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21580 ->
                                   let uu____21587 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21587
                               | uu____21588 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21591 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21591
                             then
                               let uu____21596 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21598 =
                                 let uu____21600 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21600
                                  in
                               let uu____21601 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21596 uu____21598 uu____21601
                             else ());
                            r1))
                     in
                  let uu____21606 =
                    let uu____21623 = maybe_eta t1  in
                    let uu____21630 = maybe_eta t2  in
                    (uu____21623, uu____21630)  in
                  (match uu____21606 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21672 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21672.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21672.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21672.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21672.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21672.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21672.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21672.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21672.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21693 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21693
                       then
                         let uu____21696 = destruct_flex_t not_abs wl  in
                         (match uu____21696 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21713 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21713.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21713.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21713.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21713.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21713.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21713.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21713.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21713.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21716 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21716 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21739 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21739
                       then
                         let uu____21742 = destruct_flex_t not_abs wl  in
                         (match uu____21742 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21759 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21759.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21759.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21759.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21759.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21759.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21759.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21759.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21759.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21762 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21762 orig))
                   | uu____21765 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21795 =
                    let uu____21800 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21800 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3061_21828 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21828.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21828.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21830 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21830.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21830.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21831,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3061_21846 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21846.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21846.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21848 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21848.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21848.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21849 -> (x1, x2)  in
                  (match uu____21795 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21868 = as_refinement false env t11  in
                       (match uu____21868 with
                        | (x12,phi11) ->
                            let uu____21876 = as_refinement false env t21  in
                            (match uu____21876 with
                             | (x22,phi21) ->
                                 ((let uu____21885 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21885
                                   then
                                     ((let uu____21890 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21892 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21894 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21890
                                         uu____21892 uu____21894);
                                      (let uu____21897 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21899 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21901 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21897
                                         uu____21899 uu____21901))
                                   else ());
                                  (let uu____21906 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21906 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp1 imp phi13 phi23 =
                                         let uu____21977 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____21977
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____21989 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp1 FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp1 FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____22002 =
                                            let uu____22005 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22005
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22002
                                            (p_guard base_prob));
                                         (let uu____22024 =
                                            let uu____22027 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22027
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22024
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22046 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22046)
                                          in
                                       let has_uvars =
                                         (let uu____22051 =
                                            let uu____22053 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22053
                                             in
                                          Prims.op_Negation uu____22051) ||
                                           (let uu____22057 =
                                              let uu____22059 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22059
                                               in
                                            Prims.op_Negation uu____22057)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22063 =
                                           let uu____22068 =
                                             let uu____22077 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22077]  in
                                           mk_t_problem wl1 uu____22068 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22063 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22100 =
                                                solve env1
                                                  (let uu___3106_22102 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3106_22102.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3106_22102.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3106_22102.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3106_22102.tcenv);
                                                     wl_implicits =
                                                       (uu___3106_22102.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22100 with
                                               | Failed (prob,msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    if
                                                      ((Prims.op_Negation
                                                          env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                         && has_uvars)
                                                        ||
                                                        (Prims.op_Negation
                                                           wl2.smt_ok)
                                                    then giveup env1 msg prob
                                                    else fallback ())
                                               | Success uu____22117 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22126 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22126
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3119_22135 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3119_22135.attempting);
                                                         wl_deferred =
                                                           (uu___3119_22135.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3119_22135.defer_ok);
                                                         smt_ok =
                                                           (uu___3119_22135.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3119_22135.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3119_22135.tcenv);
                                                         wl_implicits =
                                                           (uu___3119_22135.wl_implicits)
                                                       }  in
                                                     let uu____22137 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22137))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22140,FStar_Syntax_Syntax.Tm_uvar uu____22141) ->
                  let uu____22166 = destruct_flex_t t1 wl  in
                  (match uu____22166 with
                   | (f1,wl1) ->
                       let uu____22173 = destruct_flex_t t2 wl1  in
                       (match uu____22173 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22180;
                    FStar_Syntax_Syntax.pos = uu____22181;
                    FStar_Syntax_Syntax.vars = uu____22182;_},uu____22183),FStar_Syntax_Syntax.Tm_uvar
                 uu____22184) ->
                  let uu____22233 = destruct_flex_t t1 wl  in
                  (match uu____22233 with
                   | (f1,wl1) ->
                       let uu____22240 = destruct_flex_t t2 wl1  in
                       (match uu____22240 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22247,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22248;
                    FStar_Syntax_Syntax.pos = uu____22249;
                    FStar_Syntax_Syntax.vars = uu____22250;_},uu____22251))
                  ->
                  let uu____22300 = destruct_flex_t t1 wl  in
                  (match uu____22300 with
                   | (f1,wl1) ->
                       let uu____22307 = destruct_flex_t t2 wl1  in
                       (match uu____22307 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22314;
                    FStar_Syntax_Syntax.pos = uu____22315;
                    FStar_Syntax_Syntax.vars = uu____22316;_},uu____22317),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22318;
                    FStar_Syntax_Syntax.pos = uu____22319;
                    FStar_Syntax_Syntax.vars = uu____22320;_},uu____22321))
                  ->
                  let uu____22394 = destruct_flex_t t1 wl  in
                  (match uu____22394 with
                   | (f1,wl1) ->
                       let uu____22401 = destruct_flex_t t2 wl1  in
                       (match uu____22401 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22408,uu____22409) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22422 = destruct_flex_t t1 wl  in
                  (match uu____22422 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22429;
                    FStar_Syntax_Syntax.pos = uu____22430;
                    FStar_Syntax_Syntax.vars = uu____22431;_},uu____22432),uu____22433)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22470 = destruct_flex_t t1 wl  in
                  (match uu____22470 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22477,FStar_Syntax_Syntax.Tm_uvar uu____22478) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22491,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22492;
                    FStar_Syntax_Syntax.pos = uu____22493;
                    FStar_Syntax_Syntax.vars = uu____22494;_},uu____22495))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22532,FStar_Syntax_Syntax.Tm_arrow uu____22533) ->
                  solve_t' env
                    (let uu___3219_22561 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22561.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22561.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22561.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22561.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22561.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22561.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22561.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22561.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22561.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22562;
                    FStar_Syntax_Syntax.pos = uu____22563;
                    FStar_Syntax_Syntax.vars = uu____22564;_},uu____22565),FStar_Syntax_Syntax.Tm_arrow
                 uu____22566) ->
                  solve_t' env
                    (let uu___3219_22618 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22618.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22618.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22618.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22618.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22618.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22618.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22618.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22618.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22618.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22619,FStar_Syntax_Syntax.Tm_uvar uu____22620) ->
                  let uu____22633 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22633
              | (uu____22634,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22635;
                    FStar_Syntax_Syntax.pos = uu____22636;
                    FStar_Syntax_Syntax.vars = uu____22637;_},uu____22638))
                  ->
                  let uu____22675 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22675
              | (FStar_Syntax_Syntax.Tm_uvar uu____22676,uu____22677) ->
                  let uu____22690 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22690
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22691;
                    FStar_Syntax_Syntax.pos = uu____22692;
                    FStar_Syntax_Syntax.vars = uu____22693;_},uu____22694),uu____22695)
                  ->
                  let uu____22732 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22732
              | (FStar_Syntax_Syntax.Tm_refine uu____22733,uu____22734) ->
                  let t21 =
                    let uu____22742 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22742  in
                  solve_t env
                    (let uu___3254_22768 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22768.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3254_22768.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22768.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22768.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22768.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22768.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22768.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22768.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22768.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22769,FStar_Syntax_Syntax.Tm_refine uu____22770) ->
                  let t11 =
                    let uu____22778 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22778  in
                  solve_t env
                    (let uu___3261_22804 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3261_22804.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3261_22804.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3261_22804.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3261_22804.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3261_22804.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3261_22804.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3261_22804.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3261_22804.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3261_22804.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22886 =
                    let uu____22887 = guard_of_prob env wl problem t1 t2  in
                    match uu____22887 with
                    | (guard,wl1) ->
                        let uu____22894 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22894
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23113 = br1  in
                        (match uu____23113 with
                         | (p1,w1,uu____23142) ->
                             let uu____23159 = br2  in
                             (match uu____23159 with
                              | (p2,w2,uu____23182) ->
                                  let uu____23187 =
                                    let uu____23189 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23189  in
                                  if uu____23187
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23216 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23216 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23253 = br2  in
                                         (match uu____23253 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23286 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23286
                                                 in
                                              let uu____23291 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23322,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23343) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23402 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23402 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23291
                                                (fun uu____23474  ->
                                                   match uu____23474 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23511 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23511
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23532
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23532
                                                              then
                                                                let uu____23537
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23539
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23537
                                                                  uu____23539
                                                              else ());
                                                             (let uu____23545
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23545
                                                                (fun
                                                                   uu____23581
                                                                    ->
                                                                   match uu____23581
                                                                   with
                                                                   | 
                                                                   (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____23710 -> FStar_Pervasives_Native.None  in
                  let uu____23751 = solve_branches wl brs1 brs2  in
                  (match uu____23751 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23777 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23777 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23804 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23804 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23838 =
                                FStar_List.map
                                  (fun uu____23850  ->
                                     match uu____23850 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23838  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23859 =
                              let uu____23860 =
                                let uu____23861 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23861
                                  (let uu___3360_23869 = wl3  in
                                   {
                                     attempting =
                                       (uu___3360_23869.attempting);
                                     wl_deferred =
                                       (uu___3360_23869.wl_deferred);
                                     ctr = (uu___3360_23869.ctr);
                                     defer_ok = (uu___3360_23869.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3360_23869.umax_heuristic_ok);
                                     tcenv = (uu___3360_23869.tcenv);
                                     wl_implicits =
                                       (uu___3360_23869.wl_implicits)
                                   })
                                 in
                              solve env uu____23860  in
                            (match uu____23859 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23874 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23883 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23883 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23886,uu____23887) ->
                  let head1 =
                    let uu____23911 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23911
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23957 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23957
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24003 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24003
                    then
                      let uu____24007 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24009 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24011 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24007 uu____24009 uu____24011
                    else ());
                   (let no_free_uvars t =
                      (let uu____24025 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24025) &&
                        (let uu____24029 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24029)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24048 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24048 = FStar_Syntax_Util.Equal  in
                    let uu____24049 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24049
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24053 = equal t1 t2  in
                         (if uu____24053
                          then
                            let uu____24056 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24056
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24061 =
                            let uu____24068 = equal t1 t2  in
                            if uu____24068
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24081 = mk_eq2 wl env orig t1 t2  in
                               match uu____24081 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24061 with
                          | (guard,wl1) ->
                              let uu____24102 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24102))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24105,uu____24106) ->
                  let head1 =
                    let uu____24114 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24114
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24160 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24160
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24206 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24206
                    then
                      let uu____24210 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24212 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24214 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24210 uu____24212 uu____24214
                    else ());
                   (let no_free_uvars t =
                      (let uu____24228 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24228) &&
                        (let uu____24232 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24232)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24251 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24251 = FStar_Syntax_Util.Equal  in
                    let uu____24252 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24252
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24256 = equal t1 t2  in
                         (if uu____24256
                          then
                            let uu____24259 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24259
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24264 =
                            let uu____24271 = equal t1 t2  in
                            if uu____24271
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24284 = mk_eq2 wl env orig t1 t2  in
                               match uu____24284 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24264 with
                          | (guard,wl1) ->
                              let uu____24305 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24305))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24308,uu____24309) ->
                  let head1 =
                    let uu____24311 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24311
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24357 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24357
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24403 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24403
                    then
                      let uu____24407 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24409 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24411 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24407 uu____24409 uu____24411
                    else ());
                   (let no_free_uvars t =
                      (let uu____24425 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24425) &&
                        (let uu____24429 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24429)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24448 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24448 = FStar_Syntax_Util.Equal  in
                    let uu____24449 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24449
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24453 = equal t1 t2  in
                         (if uu____24453
                          then
                            let uu____24456 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24456
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24461 =
                            let uu____24468 = equal t1 t2  in
                            if uu____24468
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24481 = mk_eq2 wl env orig t1 t2  in
                               match uu____24481 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24461 with
                          | (guard,wl1) ->
                              let uu____24502 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24502))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24505,uu____24506) ->
                  let head1 =
                    let uu____24508 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24508
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24554 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24554
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24600 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24600
                    then
                      let uu____24604 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24606 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24608 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24604 uu____24606 uu____24608
                    else ());
                   (let no_free_uvars t =
                      (let uu____24622 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24622) &&
                        (let uu____24626 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24626)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24645 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24645 = FStar_Syntax_Util.Equal  in
                    let uu____24646 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24646
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24650 = equal t1 t2  in
                         (if uu____24650
                          then
                            let uu____24653 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24653
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24658 =
                            let uu____24665 = equal t1 t2  in
                            if uu____24665
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24678 = mk_eq2 wl env orig t1 t2  in
                               match uu____24678 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24658 with
                          | (guard,wl1) ->
                              let uu____24699 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24699))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24702,uu____24703) ->
                  let head1 =
                    let uu____24705 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24705
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24751 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24751
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24797 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24797
                    then
                      let uu____24801 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24803 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24805 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24801 uu____24803 uu____24805
                    else ());
                   (let no_free_uvars t =
                      (let uu____24819 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24819) &&
                        (let uu____24823 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24823)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24842 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24842 = FStar_Syntax_Util.Equal  in
                    let uu____24843 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24843
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24847 = equal t1 t2  in
                         (if uu____24847
                          then
                            let uu____24850 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24850
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24855 =
                            let uu____24862 = equal t1 t2  in
                            if uu____24862
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24875 = mk_eq2 wl env orig t1 t2  in
                               match uu____24875 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24855 with
                          | (guard,wl1) ->
                              let uu____24896 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24896))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24899,uu____24900) ->
                  let head1 =
                    let uu____24918 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24918
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24964 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24964
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25010 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25010
                    then
                      let uu____25014 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25016 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25018 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25014 uu____25016 uu____25018
                    else ());
                   (let no_free_uvars t =
                      (let uu____25032 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25032) &&
                        (let uu____25036 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25036)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25055 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25055 = FStar_Syntax_Util.Equal  in
                    let uu____25056 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25056
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25060 = equal t1 t2  in
                         (if uu____25060
                          then
                            let uu____25063 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25063
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25068 =
                            let uu____25075 = equal t1 t2  in
                            if uu____25075
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25088 = mk_eq2 wl env orig t1 t2  in
                               match uu____25088 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25068 with
                          | (guard,wl1) ->
                              let uu____25109 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25109))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25112,FStar_Syntax_Syntax.Tm_match uu____25113) ->
                  let head1 =
                    let uu____25137 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25137
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25183 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25183
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25229 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25229
                    then
                      let uu____25233 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25235 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25237 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25233 uu____25235 uu____25237
                    else ());
                   (let no_free_uvars t =
                      (let uu____25251 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25251) &&
                        (let uu____25255 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25255)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25274 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25274 = FStar_Syntax_Util.Equal  in
                    let uu____25275 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25275
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25279 = equal t1 t2  in
                         (if uu____25279
                          then
                            let uu____25282 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25282
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25287 =
                            let uu____25294 = equal t1 t2  in
                            if uu____25294
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25307 = mk_eq2 wl env orig t1 t2  in
                               match uu____25307 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25287 with
                          | (guard,wl1) ->
                              let uu____25328 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25328))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25331,FStar_Syntax_Syntax.Tm_uinst uu____25332) ->
                  let head1 =
                    let uu____25340 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25340
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25386 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25386
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25432 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25432
                    then
                      let uu____25436 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25438 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25440 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25436 uu____25438 uu____25440
                    else ());
                   (let no_free_uvars t =
                      (let uu____25454 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25454) &&
                        (let uu____25458 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25458)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25477 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25477 = FStar_Syntax_Util.Equal  in
                    let uu____25478 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25478
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25482 = equal t1 t2  in
                         (if uu____25482
                          then
                            let uu____25485 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25485
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25490 =
                            let uu____25497 = equal t1 t2  in
                            if uu____25497
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25510 = mk_eq2 wl env orig t1 t2  in
                               match uu____25510 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25490 with
                          | (guard,wl1) ->
                              let uu____25531 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25531))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25534,FStar_Syntax_Syntax.Tm_name uu____25535) ->
                  let head1 =
                    let uu____25537 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25537
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25583 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25583
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25623 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25623
                    then
                      let uu____25627 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25629 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25631 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25627 uu____25629 uu____25631
                    else ());
                   (let no_free_uvars t =
                      (let uu____25645 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25645) &&
                        (let uu____25649 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25649)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25668 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25668 = FStar_Syntax_Util.Equal  in
                    let uu____25669 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25669
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25673 = equal t1 t2  in
                         (if uu____25673
                          then
                            let uu____25676 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25676
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25681 =
                            let uu____25688 = equal t1 t2  in
                            if uu____25688
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25701 = mk_eq2 wl env orig t1 t2  in
                               match uu____25701 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25681 with
                          | (guard,wl1) ->
                              let uu____25722 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25722))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25725,FStar_Syntax_Syntax.Tm_constant uu____25726) ->
                  let head1 =
                    let uu____25728 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25728
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25768 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25768
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25808 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25808
                    then
                      let uu____25812 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25814 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25816 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25812 uu____25814 uu____25816
                    else ());
                   (let no_free_uvars t =
                      (let uu____25830 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25830) &&
                        (let uu____25834 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25834)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25853 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25853 = FStar_Syntax_Util.Equal  in
                    let uu____25854 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25854
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25858 = equal t1 t2  in
                         (if uu____25858
                          then
                            let uu____25861 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25861
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25866 =
                            let uu____25873 = equal t1 t2  in
                            if uu____25873
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25886 = mk_eq2 wl env orig t1 t2  in
                               match uu____25886 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25866 with
                          | (guard,wl1) ->
                              let uu____25907 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25907))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25910,FStar_Syntax_Syntax.Tm_fvar uu____25911) ->
                  let head1 =
                    let uu____25913 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25913
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25959 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25959
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26005 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26005
                    then
                      let uu____26009 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26011 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26013 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26009 uu____26011 uu____26013
                    else ());
                   (let no_free_uvars t =
                      (let uu____26027 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26027) &&
                        (let uu____26031 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26031)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26050 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26050 = FStar_Syntax_Util.Equal  in
                    let uu____26051 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26051
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26055 = equal t1 t2  in
                         (if uu____26055
                          then
                            let uu____26058 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26058
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26063 =
                            let uu____26070 = equal t1 t2  in
                            if uu____26070
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26083 = mk_eq2 wl env orig t1 t2  in
                               match uu____26083 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26063 with
                          | (guard,wl1) ->
                              let uu____26104 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26104))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26107,FStar_Syntax_Syntax.Tm_app uu____26108) ->
                  let head1 =
                    let uu____26126 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26126
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26166 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26166
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26206 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26206
                    then
                      let uu____26210 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26212 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26214 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26210 uu____26212 uu____26214
                    else ());
                   (let no_free_uvars t =
                      (let uu____26228 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26228) &&
                        (let uu____26232 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26232)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26251 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26251 = FStar_Syntax_Util.Equal  in
                    let uu____26252 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26252
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26256 = equal t1 t2  in
                         (if uu____26256
                          then
                            let uu____26259 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26259
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26264 =
                            let uu____26271 = equal t1 t2  in
                            if uu____26271
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26284 = mk_eq2 wl env orig t1 t2  in
                               match uu____26284 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26264 with
                          | (guard,wl1) ->
                              let uu____26305 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26305))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26308,FStar_Syntax_Syntax.Tm_let uu____26309) ->
                  let uu____26336 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26336
                  then
                    let uu____26339 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26339
                  else
                    (let uu____26342 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26342 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26345,uu____26346) ->
                  let uu____26360 =
                    let uu____26366 =
                      let uu____26368 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26370 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26372 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26374 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26368 uu____26370 uu____26372 uu____26374
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26366)
                     in
                  FStar_Errors.raise_error uu____26360
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26378,FStar_Syntax_Syntax.Tm_let uu____26379) ->
                  let uu____26393 =
                    let uu____26399 =
                      let uu____26401 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26403 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26405 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26407 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26401 uu____26403 uu____26405 uu____26407
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26399)
                     in
                  FStar_Errors.raise_error uu____26393
                    t1.FStar_Syntax_Syntax.pos
              | uu____26411 ->
                  let uu____26416 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26416 orig))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp g_lift =
          (let uu____26482 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26482
           then
             let uu____26487 =
               let uu____26489 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26489  in
             let uu____26490 =
               let uu____26492 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26492  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26487 uu____26490
           else ());
          (let uu____26496 =
             let uu____26498 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26498  in
           if uu____26496
           then
             let uu____26501 =
               mklstr
                 (fun uu____26508  ->
                    let uu____26509 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26511 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26509 uu____26511)
                in
             giveup env uu____26501 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26533 =
                  mklstr
                    (fun uu____26540  ->
                       let uu____26541 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26543 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26541 uu____26543)
                   in
                giveup env uu____26533 orig)
             else
               (let uu____26548 =
                  FStar_List.fold_left2
                    (fun uu____26569  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26569 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26590 =
                                 let uu____26595 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26596 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26595
                                   FStar_TypeChecker_Common.EQ uu____26596
                                   "effect universes"
                                  in
                               (match uu____26590 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26548 with
                | (univ_sub_probs,wl1) ->
                    let uu____26616 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26616 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26624 =
                           FStar_List.fold_right2
                             (fun uu____26661  ->
                                fun uu____26662  ->
                                  fun uu____26663  ->
                                    match (uu____26661, uu____26662,
                                            uu____26663)
                                    with
                                    | ((a1,uu____26707),(a2,uu____26709),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26742 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26742 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26624 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26769 =
                                  let uu____26772 =
                                    let uu____26775 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26775
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26772
                                   in
                                FStar_List.append univ_sub_probs uu____26769
                                 in
                              let guard =
                                let guard =
                                  let uu____26797 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26797  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3512_26806 = wl3  in
                                {
                                  attempting = (uu___3512_26806.attempting);
                                  wl_deferred = (uu___3512_26806.wl_deferred);
                                  ctr = (uu___3512_26806.ctr);
                                  defer_ok = (uu___3512_26806.defer_ok);
                                  smt_ok = (uu___3512_26806.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3512_26806.umax_heuristic_ok);
                                  tcenv = (uu___3512_26806.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26808 = attempt sub_probs wl5  in
                              solve env uu____26808))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26826 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26826
           then
             let uu____26831 =
               let uu____26833 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26833
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26835 =
               let uu____26837 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26837
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26831 uu____26835
           else ());
          (let uu____26842 =
             let uu____26847 =
               let uu____26852 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26852
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26847
               (fun uu____26869  ->
                  match uu____26869 with
                  | (c,g) ->
                      let uu____26880 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26880, g))
              in
           match uu____26842 with
           | (c12,g_lift) ->
               ((let uu____26884 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26884
                 then
                   let uu____26889 =
                     let uu____26891 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26891
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26893 =
                     let uu____26895 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26895
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26889 uu____26893
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3532_26905 = wl  in
                     {
                       attempting = (uu___3532_26905.attempting);
                       wl_deferred = (uu___3532_26905.wl_deferred);
                       ctr = (uu___3532_26905.ctr);
                       defer_ok = (uu___3532_26905.defer_ok);
                       smt_ok = (uu___3532_26905.smt_ok);
                       umax_heuristic_ok =
                         (uu___3532_26905.umax_heuristic_ok);
                       tcenv = (uu___3532_26905.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26906 =
                     let rec is_uvar1 t =
                       let uu____26920 =
                         let uu____26921 = FStar_Syntax_Subst.compress t  in
                         uu____26921.FStar_Syntax_Syntax.n  in
                       match uu____26920 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26925 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26940) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26946) ->
                           is_uvar1 t1
                       | uu____26971 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27005  ->
                          fun uu____27006  ->
                            fun uu____27007  ->
                              match (uu____27005, uu____27006, uu____27007)
                              with
                              | ((a1,uu____27051),(a2,uu____27053),(is_sub_probs,wl2))
                                  ->
                                  let uu____27086 = is_uvar1 a1  in
                                  if uu____27086
                                  then
                                    ((let uu____27096 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27096
                                      then
                                        let uu____27101 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27103 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27101 uu____27103
                                      else ());
                                     (let uu____27108 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27108 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26906 with
                   | (is_sub_probs,wl2) ->
                       let uu____27136 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27136 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27144 =
                              let uu____27149 =
                                let uu____27150 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27150
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27149
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27144 with
                             | (uu____27157,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27168 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27170 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27168 s uu____27170
                                    in
                                 let uu____27173 =
                                   let uu____27202 =
                                     let uu____27203 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27203.FStar_Syntax_Syntax.n  in
                                   match uu____27202 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27263 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27263 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27326 =
                                              let uu____27345 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27345
                                                (fun uu____27449  ->
                                                   match uu____27449 with
                                                   | (l1,l2) ->
                                                       let uu____27522 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27522))
                                               in
                                            (match uu____27326 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27627 ->
                                       let uu____27628 =
                                         let uu____27634 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27634)
                                          in
                                       FStar_Errors.raise_error uu____27628 r
                                    in
                                 (match uu____27173 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27710 =
                                        let uu____27717 =
                                          let uu____27718 =
                                            let uu____27719 =
                                              let uu____27726 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27726,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27719
                                             in
                                          [uu____27718]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27717
                                          (fun b  ->
                                             let uu____27742 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27744 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27746 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27742 uu____27744
                                               uu____27746) r
                                         in
                                      (match uu____27710 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27756 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27756
                                             then
                                               let uu____27761 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27770 =
                                                          let uu____27772 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27772
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27770) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27761
                                             else ());
                                            (let wl4 =
                                               let uu___3604_27780 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3604_27780.attempting);
                                                 wl_deferred =
                                                   (uu___3604_27780.wl_deferred);
                                                 ctr = (uu___3604_27780.ctr);
                                                 defer_ok =
                                                   (uu___3604_27780.defer_ok);
                                                 smt_ok =
                                                   (uu___3604_27780.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3604_27780.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3604_27780.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27805 =
                                                        let uu____27812 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27812, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27805) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27829 =
                                               let f_sort_is =
                                                 let uu____27839 =
                                                   let uu____27840 =
                                                     let uu____27843 =
                                                       let uu____27844 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27844.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27843
                                                      in
                                                   uu____27840.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27839 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27855,uu____27856::is)
                                                     ->
                                                     let uu____27898 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27898
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27931 ->
                                                     let uu____27932 =
                                                       let uu____27938 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27938)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27932 r
                                                  in
                                               let uu____27944 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____27979  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____27979
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28000 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28000
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27944
                                                in
                                             match uu____27829 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28025 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28025
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28026 =
                                                   let g_sort_is =
                                                     let uu____28036 =
                                                       let uu____28037 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28037.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28036 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28042,uu____28043::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28103 ->
                                                         let uu____28104 =
                                                           let uu____28110 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28110)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28104 r
                                                      in
                                                   let uu____28116 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28151  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28151
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28172
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28172
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28116
                                                    in
                                                 (match uu____28026 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28199 =
                                                          let uu____28204 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28205 =
                                                            let uu____28206 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28206
                                                             in
                                                          (uu____28204,
                                                            uu____28205)
                                                           in
                                                        match uu____28199
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28234 =
                                                          let uu____28237 =
                                                            let uu____28240 =
                                                              let uu____28243
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28243
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28240
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28237
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28234
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28267 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28267
                                                           in
                                                        match g_lift.FStar_TypeChecker_Common.guard_f
                                                        with
                                                        | FStar_TypeChecker_Common.Trivial
                                                             -> guard
                                                        | FStar_TypeChecker_Common.NonTrivial
                                                            f ->
                                                            FStar_Syntax_Util.mk_conj
                                                              guard f
                                                         in
                                                      let wl7 =
                                                        let uu____28278 =
                                                          let uu____28281 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28284  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28284)
                                                            uu____28281
                                                           in
                                                        solve_prob orig
                                                          uu____28278 [] wl6
                                                         in
                                                      let uu____28285 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28285))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28308 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28310 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28310]
              | x -> x  in
            let c12 =
              let uu___3670_28313 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3670_28313.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3670_28313.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3670_28313.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3670_28313.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28314 =
              let uu____28319 =
                FStar_All.pipe_right
                  (let uu___3673_28321 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3673_28321.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3673_28321.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3673_28321.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3673_28321.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28319
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28314
              (fun uu____28335  ->
                 match uu____28335 with
                 | (c,g) ->
                     let uu____28342 =
                       let uu____28344 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28344  in
                     if uu____28342
                     then
                       let uu____28347 =
                         let uu____28353 =
                           let uu____28355 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28357 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28355 uu____28357
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28353)
                          in
                       FStar_Errors.raise_error uu____28347 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28363 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28363
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28369 = lift_c1 ()  in
               solve_eq uu____28369 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28378  ->
                         match uu___31_28378 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28383 -> false))
                  in
               let uu____28385 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28415)::uu____28416,(wp2,uu____28418)::uu____28419)
                     -> (wp1, wp2)
                 | uu____28492 ->
                     let uu____28517 =
                       let uu____28523 =
                         let uu____28525 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28527 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28525 uu____28527
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28523)
                        in
                     FStar_Errors.raise_error uu____28517
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28385 with
               | (wpc1,wpc2) ->
                   let uu____28537 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28537
                   then
                     let uu____28540 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28540 wl
                   else
                     (let uu____28544 =
                        let uu____28551 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28551  in
                      match uu____28544 with
                      | (c2_decl,qualifiers) ->
                          let uu____28572 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28572
                          then
                            let c1_repr =
                              let uu____28579 =
                                let uu____28580 =
                                  let uu____28581 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28581  in
                                let uu____28582 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28580 uu____28582
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28579
                               in
                            let c2_repr =
                              let uu____28585 =
                                let uu____28586 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28587 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28586 uu____28587
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28585
                               in
                            let uu____28589 =
                              let uu____28594 =
                                let uu____28596 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28598 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28596
                                  uu____28598
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28594
                               in
                            (match uu____28589 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28604 = attempt [prob] wl2  in
                                 solve env uu____28604)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28624 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28624
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28647 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28647
                                      then
                                        FStar_Util.print_string
                                          "Using trivial wp ... \n"
                                      else ());
                                     (let c1_univ =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env
                                          c11.FStar_Syntax_Syntax.result_typ
                                         in
                                      let trivial =
                                        let uu____28657 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28657 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28664 =
                                        let uu____28665 =
                                          let uu____28682 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [c1_univ] env c2_decl trivial
                                             in
                                          let uu____28685 =
                                            let uu____28696 =
                                              FStar_Syntax_Syntax.as_arg
                                                c11.FStar_Syntax_Syntax.result_typ
                                               in
                                            [uu____28696; wpc1_2]  in
                                          (uu____28682, uu____28685)  in
                                        FStar_Syntax_Syntax.Tm_app
                                          uu____28665
                                         in
                                      FStar_Syntax_Syntax.mk uu____28664 r))
                                  else
                                    (let c2_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c21.FStar_Syntax_Syntax.result_typ
                                        in
                                     let stronger =
                                       FStar_All.pipe_right c2_decl
                                         FStar_Syntax_Util.get_stronger_vc_combinator
                                        in
                                     let uu____28745 =
                                       let uu____28746 =
                                         let uu____28763 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c2_univ] env c2_decl stronger
                                            in
                                         let uu____28766 =
                                           let uu____28777 =
                                             FStar_Syntax_Syntax.as_arg
                                               c21.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____28786 =
                                             let uu____28797 =
                                               FStar_Syntax_Syntax.as_arg
                                                 wpc2
                                                in
                                             [uu____28797; wpc1_2]  in
                                           uu____28777 :: uu____28786  in
                                         (uu____28763, uu____28766)  in
                                       FStar_Syntax_Syntax.Tm_app uu____28746
                                        in
                                     FStar_Syntax_Syntax.mk uu____28745 r))
                                in
                             (let uu____28851 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28851
                              then
                                let uu____28856 =
                                  let uu____28858 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28858
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28856
                              else ());
                             (let uu____28862 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28862 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28871 =
                                      let uu____28874 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28877  ->
                                           FStar_Pervasives_Native.Some
                                             _28877) uu____28874
                                       in
                                    solve_prob orig uu____28871 [] wl1  in
                                  let uu____28878 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28878))))
           in
        let uu____28879 = FStar_Util.physical_equality c1 c2  in
        if uu____28879
        then
          let uu____28882 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28882
        else
          ((let uu____28886 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28886
            then
              let uu____28891 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28893 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28891
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28893
            else ());
           (let uu____28898 =
              let uu____28907 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28910 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28907, uu____28910)  in
            match uu____28898 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28928),FStar_Syntax_Syntax.Total
                    (t2,uu____28930)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28947 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28947 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28949,FStar_Syntax_Syntax.Total uu____28950) ->
                     let uu____28967 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____28967 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28971),FStar_Syntax_Syntax.Total
                    (t2,uu____28973)) ->
                     let uu____28990 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28990 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28993),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28995)) ->
                     let uu____29012 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29012 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29015),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29017)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29034 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29034 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29037),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29039)) ->
                     let uu____29056 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29056 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29059,FStar_Syntax_Syntax.Comp uu____29060) ->
                     let uu____29069 =
                       let uu___3797_29072 = problem  in
                       let uu____29075 =
                         let uu____29076 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29076
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29072.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29075;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29072.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29072.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29072.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29072.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29072.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29072.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29072.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29072.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29069 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29077,FStar_Syntax_Syntax.Comp uu____29078) ->
                     let uu____29087 =
                       let uu___3797_29090 = problem  in
                       let uu____29093 =
                         let uu____29094 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29094
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29090.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29093;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29090.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29090.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29090.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29090.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29090.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29090.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29090.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29090.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29087 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29095,FStar_Syntax_Syntax.GTotal uu____29096) ->
                     let uu____29105 =
                       let uu___3809_29108 = problem  in
                       let uu____29111 =
                         let uu____29112 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29112
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29108.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29108.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29108.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29111;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29108.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29108.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29108.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29108.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29108.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29108.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29105 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29113,FStar_Syntax_Syntax.Total uu____29114) ->
                     let uu____29123 =
                       let uu___3809_29126 = problem  in
                       let uu____29129 =
                         let uu____29130 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29130
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29126.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29126.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29126.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29129;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29126.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29126.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29126.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29126.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29126.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29126.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29123 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29131,FStar_Syntax_Syntax.Comp uu____29132) ->
                     let uu____29133 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____29133
                     then
                       let uu____29136 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29136 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29143 =
                            let uu____29148 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29148
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29157 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29158 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29157, uu____29158))
                             in
                          match uu____29143 with
                          | (c1_comp1,c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____29166 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29166
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29174 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29174 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29177 =
                                  mklstr
                                    (fun uu____29184  ->
                                       let uu____29185 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29187 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29185 uu____29187)
                                   in
                                giveup env uu____29177 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29198 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29198 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29248 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29248 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29273 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29304  ->
                match uu____29304 with
                | (u1,u2) ->
                    let uu____29312 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29314 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29312 uu____29314))
         in
      FStar_All.pipe_right uu____29273 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29351,[])) when
          let uu____29378 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29378 -> "{}"
      | uu____29381 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29408 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29408
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29420 =
              FStar_List.map
                (fun uu____29433  ->
                   match uu____29433 with
                   | (uu____29440,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29420 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29451 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29451 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____29508 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29508
                  then
                    let uu____29516 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29518 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29516
                      (rel_to_string rel) uu____29518
                  else "TOP"  in
                let uu____29524 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29524 with
                | (p,wl1) ->
                    (def_check_prob (Prims.op_Hat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv *
              worklist))
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____29584 =
                let uu____29587 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29590  -> FStar_Pervasives_Native.Some _29590)
                  uu____29587
                 in
              FStar_Syntax_Syntax.new_bv uu____29584 t1  in
            let uu____29591 =
              let uu____29596 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29596
               in
            match uu____29591 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____29654 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29654
         then
           let uu____29659 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29659
         else ());
        (let uu____29666 =
           FStar_Util.record_time (fun uu____29673  -> solve env probs)  in
         match uu____29666 with
         | (sol,ms) ->
             ((let uu____29685 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29685
               then
                 let uu____29690 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29690
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29703 =
                     FStar_Util.record_time
                       (fun uu____29710  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29703 with
                    | ((),ms1) ->
                        ((let uu____29721 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29721
                          then
                            let uu____29726 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29726
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29738 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29738
                     then
                       let uu____29745 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29745
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____29771 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29771
            then
              let uu____29776 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29776
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29784 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29784
             then
               let uu____29789 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29789
             else ());
            (let f2 =
               let uu____29795 =
                 let uu____29796 = FStar_Syntax_Util.unmeta f1  in
                 uu____29796.FStar_Syntax_Syntax.n  in
               match uu____29795 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29800 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3926_29801 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3926_29801.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3926_29801.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3926_29801.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred *
        FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____29844 =
              let uu____29845 =
                let uu____29846 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29847  ->
                       FStar_TypeChecker_Common.NonTrivial _29847)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29846;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29845  in
            FStar_All.pipe_left
              (fun _29854  -> FStar_Pervasives_Native.Some _29854)
              uu____29844
  
let with_guard_no_simp :
  'Auu____29864 .
    'Auu____29864 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____29904 =
              let uu____29905 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29906  -> FStar_TypeChecker_Common.NonTrivial _29906)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29905;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29904
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____29939 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29939
           then
             let uu____29944 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29946 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29944
               uu____29946
           else ());
          (let uu____29951 =
             let uu____29956 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29956
              in
           match uu____29951 with
           | (prob,wl) ->
               let g =
                 let uu____29964 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29972  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29964  in
               ((let uu____29990 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29990
                 then
                   let uu____29995 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29995
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30016 = try_teq true env t1 t2  in
        match uu____30016 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30021 = FStar_TypeChecker_Env.get_range env  in
              let uu____30022 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30021 uu____30022);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30030 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30030
              then
                let uu____30035 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30037 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30039 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30035
                  uu____30037 uu____30039
              else ());
             g)
  
let (get_teq_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30063 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30063
         then
           let uu____30068 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30070 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30068
             uu____30070
         else ());
        (let uu____30075 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30075 with
         | (prob,x,wl) ->
             let g =
               let uu____30090 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30099  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30090  in
             ((let uu____30117 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30117
               then
                 let uu____30122 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30122
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30130 =
                     let uu____30131 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30131 g1  in
                   FStar_Pervasives_Native.Some uu____30130)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30153 = FStar_TypeChecker_Env.get_range env  in
          let uu____30154 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30153 uu____30154
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____30183 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30183
         then
           let uu____30188 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30190 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30188 uu____30190
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30201 =
           let uu____30208 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30208 "sub_comp"
            in
         match uu____30201 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30221 =
                 FStar_Util.record_time
                   (fun uu____30233  ->
                      let uu____30234 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30243  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30234)
                  in
               match uu____30221 with
               | (r,ms) ->
                   ((let uu____30271 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30271
                     then
                       let uu____30276 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30278 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30280 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30276 uu____30278
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30280
                     else ());
                    r))))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____30318  ->
        match uu____30318 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30361 =
                 let uu____30367 =
                   let uu____30369 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30371 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30369 uu____30371
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30367)  in
               let uu____30375 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30361 uu____30375)
               in
            let equiv1 v1 v' =
              let uu____30388 =
                let uu____30393 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30394 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30393, uu____30394)  in
              match uu____30388 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30414 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30445 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30445 with
                      | FStar_Syntax_Syntax.U_unif uu____30452 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30481  ->
                                    match uu____30481 with
                                    | (u,v') ->
                                        let uu____30490 = equiv1 v1 v'  in
                                        if uu____30490
                                        then
                                          let uu____30495 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30495 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30516 -> []))
               in
            let uu____30521 =
              let wl =
                let uu___4037_30525 = empty_worklist env  in
                {
                  attempting = (uu___4037_30525.attempting);
                  wl_deferred = (uu___4037_30525.wl_deferred);
                  ctr = (uu___4037_30525.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4037_30525.smt_ok);
                  umax_heuristic_ok = (uu___4037_30525.umax_heuristic_ok);
                  tcenv = (uu___4037_30525.tcenv);
                  wl_implicits = (uu___4037_30525.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30544  ->
                      match uu____30544 with
                      | (lb,v1) ->
                          let uu____30551 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30551 with
                           | USolved wl1 -> ()
                           | uu____30554 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30565 =
              match uu____30565 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30577) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____30601,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30603,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30614) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30622,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30631 -> false)
               in
            let uu____30637 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30654  ->
                      match uu____30654 with
                      | (u,v1) ->
                          let uu____30662 = check_ineq (u, v1)  in
                          if uu____30662
                          then true
                          else
                            ((let uu____30670 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30670
                              then
                                let uu____30675 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30677 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30675
                                  uu____30677
                              else ());
                             false)))
               in
            if uu____30637
            then ()
            else
              ((let uu____30687 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30687
                then
                  ((let uu____30693 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30693);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30705 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30705))
                else ());
               (let uu____30718 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30718))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let (try_solve_deferred_constraints :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____30791 =
          match uu____30791 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4114_30814 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4114_30814.attempting);
            wl_deferred = (uu___4114_30814.wl_deferred);
            ctr = (uu___4114_30814.ctr);
            defer_ok;
            smt_ok = (uu___4114_30814.smt_ok);
            umax_heuristic_ok = (uu___4114_30814.umax_heuristic_ok);
            tcenv = (uu___4114_30814.tcenv);
            wl_implicits = (uu___4114_30814.wl_implicits)
          }  in
        (let uu____30817 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30817
         then
           let uu____30822 = FStar_Util.string_of_bool defer_ok  in
           let uu____30824 = wl_to_string wl  in
           let uu____30826 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30822 uu____30824 uu____30826
         else ());
        (let g1 =
           let uu____30832 = solve_and_commit env wl fail1  in
           match uu____30832 with
           | FStar_Pervasives_Native.Some
               (uu____30839::uu____30840,uu____30841) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4129_30870 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4129_30870.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4129_30870.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30871 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4134_30880 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4134_30880.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4134_30880.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4134_30880.FStar_TypeChecker_Common.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___4146_30957 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4146_30957.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4146_30957.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4146_30957.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30958 =
            let uu____30960 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30960  in
          if uu____30958
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30972 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30973 =
                       let uu____30975 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30975
                        in
                     FStar_Errors.diag uu____30972 uu____30973)
                  else ();
                  (let vc1 =
                     let uu____30981 =
                       let uu____30985 =
                         let uu____30987 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____30987  in
                       FStar_Pervasives_Native.Some uu____30985  in
                     FStar_Profiling.profile
                       (fun uu____30990  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____30981 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____30994 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30995 =
                        let uu____30997 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30997
                         in
                      FStar_Errors.diag uu____30994 uu____30995)
                   else ();
                   (let uu____31003 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31003
                      "discharge_guard'" env vc1);
                   (let uu____31005 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31005 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31014 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31015 =
                                let uu____31017 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31017
                                 in
                              FStar_Errors.diag uu____31014 uu____31015)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31027 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31028 =
                                let uu____31030 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31030
                                 in
                              FStar_Errors.diag uu____31027 uu____31028)
                           else ();
                           (let vcs =
                              let uu____31044 = FStar_Options.use_tactics ()
                                 in
                              if uu____31044
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31066  ->
                                     (let uu____31068 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31068);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31112  ->
                                              match uu____31112 with
                                              | (env1,goal,opts) ->
                                                  let uu____31128 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31128, opts)))))
                              else
                                (let uu____31132 =
                                   let uu____31139 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31139)  in
                                 [uu____31132])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31172  ->
                                    match uu____31172 with
                                    | (env1,goal,opts) ->
                                        let uu____31182 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31182 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal1 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              if debug1
                                              then
                                                (let uu____31193 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31194 =
                                                   let uu____31196 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31198 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31196 uu____31198
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31193 uu____31194)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31205 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31206 =
                                                   let uu____31208 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31208
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31205 uu____31206)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31226 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31226 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31235 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31235
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31249 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31249 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31279 = try_teq false env t1 t2  in
        match uu____31279 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____31323 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31323 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31336 ->
                     let uu____31349 =
                       let uu____31350 = FStar_Syntax_Subst.compress r  in
                       uu____31350.FStar_Syntax_Syntax.n  in
                     (match uu____31349 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31355) ->
                          unresolved ctx_u'
                      | uu____31372 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31396 = acc  in
            match uu____31396 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31415 = hd1  in
                     (match uu____31415 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31426 = unresolved ctx_u  in
                             if uu____31426
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31450 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31450
                                     then
                                       let uu____31454 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31454
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31463 = teq_nosmt env1 t tm
                                          in
                                       match uu____31463 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4259_31473 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4259_31473.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4259_31473.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4259_31473.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4259_31473.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4259_31473.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4259_31473.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4259_31473.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4262_31481 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4262_31481.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4262_31481.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4262_31481.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4266_31492 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4266_31492.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4266_31492.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4266_31492.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4266_31492.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4266_31492.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4266_31492.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4266_31492.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4266_31492.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4266_31492.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4266_31492.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4266_31492.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4266_31492.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4266_31492.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4266_31492.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4266_31492.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4266_31492.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4266_31492.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4266_31492.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4266_31492.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4266_31492.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4266_31492.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4266_31492.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4266_31492.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4266_31492.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4266_31492.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4266_31492.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4266_31492.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4266_31492.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4266_31492.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4266_31492.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4266_31492.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4266_31492.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4266_31492.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4266_31492.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4266_31492.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4266_31492.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4266_31492.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4266_31492.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4266_31492.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4266_31492.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4266_31492.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4266_31492.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4266_31492.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4266_31492.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4266_31492.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4266_31492.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4271_31497 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4271_31497.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4271_31497.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4271_31497.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4271_31497.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4271_31497.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4271_31497.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4271_31497.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4271_31497.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4271_31497.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4271_31497.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4271_31497.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4271_31497.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4271_31497.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4271_31497.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4271_31497.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4271_31497.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4271_31497.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4271_31497.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4271_31497.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4271_31497.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4271_31497.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4271_31497.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4271_31497.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4271_31497.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4271_31497.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4271_31497.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4271_31497.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4271_31497.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4271_31497.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4271_31497.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4271_31497.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4271_31497.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4271_31497.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4271_31497.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4271_31497.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4271_31497.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4271_31497.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31502 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31502
                                   then
                                     let uu____31507 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31509 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31511 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31513 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31507 uu____31509 uu____31511
                                       reason uu____31513
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4277_31520  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31527 =
                                             let uu____31537 =
                                               let uu____31545 =
                                                 let uu____31547 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31549 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31551 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31547 uu____31549
                                                   uu____31551
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31545, r)
                                                in
                                             [uu____31537]  in
                                           FStar_Errors.add_errors
                                             uu____31527);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31570 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31581  ->
                                               let uu____31582 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31584 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31586 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31582 uu____31584
                                                 reason uu____31586)) env2 g1
                                         true
                                        in
                                     match uu____31570 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl1)))))
             in
          let uu___4289_31594 = g  in
          let uu____31595 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4289_31594.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4289_31594.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4289_31594.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31595
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____31635 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31635 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31636 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31636
      | imp::uu____31638 ->
          let uu____31641 =
            let uu____31647 =
              let uu____31649 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31651 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31649 uu____31651
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31647)
             in
          FStar_Errors.raise_error uu____31641
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31671 = teq env t1 t2  in
        force_trivial_guard env uu____31671
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31690 = teq_nosmt env t1 t2  in
        match uu____31690 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4314_31709 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4314_31709.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4314_31709.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4314_31709.FStar_TypeChecker_Common.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31745 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31745
         then
           let uu____31750 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31752 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31750
             uu____31752
         else ());
        (let uu____31757 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31757 with
         | (prob,x,wl) ->
             let g =
               let uu____31776 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31785  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31776  in
             ((let uu____31803 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31803
               then
                 let uu____31808 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31810 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31812 =
                   let uu____31814 = FStar_Util.must g  in
                   guard_to_string env uu____31814  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31808 uu____31810 uu____31812
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31851 = check_subtyping env t1 t2  in
        match uu____31851 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31870 =
              let uu____31871 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31871 g  in
            FStar_Pervasives_Native.Some uu____31870
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31890 = check_subtyping env t1 t2  in
        match uu____31890 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31909 =
              let uu____31910 =
                let uu____31911 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31911]  in
              FStar_TypeChecker_Env.close_guard env uu____31910 g  in
            FStar_Pervasives_Native.Some uu____31909
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31949 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31949
         then
           let uu____31954 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31956 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31954
             uu____31956
         else ());
        (let uu____31961 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31961 with
         | (prob,x,wl) ->
             let g =
               let uu____31976 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31985  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31976  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32006 =
                      let uu____32007 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32007]  in
                    FStar_TypeChecker_Env.close_guard env uu____32006 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32048 = subtype_nosmt env t1 t2  in
        match uu____32048 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  