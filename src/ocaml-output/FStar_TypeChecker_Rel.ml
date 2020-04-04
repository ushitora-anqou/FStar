open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f  ->
    let uf = FStar_Syntax_Unionfind.get ()  in
    FStar_Thunk.mk
      (fun uu____42  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         FStar_Syntax_Unionfind.set uf;
         (let r = f ()  in FStar_Syntax_Unionfind.rollback tx; r))
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____80 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____115 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  wl_deferred_to_tac:
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
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_deferred
  
let (__proj__Mkworklist__item__wl_deferred_to_tac :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_deferred_to_tac
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_implicits
  
let (as_deferred :
  (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ->
    FStar_TypeChecker_Common.deferred)
  =
  fun wl_def  ->
    FStar_List.map
      (fun uu____714  ->
         match uu____714 with
         | (uu____730,m,p) ->
             let uu____741 = FStar_Thunk.force m  in (uu____741, p)) wl_def
  
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl  ->
    fun d  ->
      FStar_List.map
        (fun uu____793  ->
           match uu____793 with
           | (m,p) ->
               let uu____813 = FStar_Thunk.mkv m  in ((wl.ctr), uu____813, p))
        d
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                FStar_Syntax_Syntax.ctx_uvar_meta_t
                  FStar_Pervasives_Native.option ->
                  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
                    worklist))
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                fun meta  ->
                  let ctx_uvar =
                    let uu____906 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____906;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    }  in
                  FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
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
                   (let uu____938 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____938
                    then
                      let uu____942 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____942
                    else ());
                   (ctx_uvar, t,
                     ((let uu___93_948 = wl  in
                       {
                         attempting = (uu___93_948.attempting);
                         wl_deferred = (uu___93_948.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___93_948.wl_deferred_to_tac);
                         ctr = (uu___93_948.ctr);
                         defer_ok = (uu___93_948.defer_ok);
                         smt_ok = (uu___93_948.smt_ok);
                         umax_heuristic_ok = (uu___93_948.umax_heuristic_ok);
                         tcenv = (uu___93_948.tcenv);
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
            let uu___99_981 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___99_981.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___99_981.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___99_981.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___99_981.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___99_981.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___99_981.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___99_981.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___99_981.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___99_981.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___99_981.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___99_981.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___99_981.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___99_981.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___99_981.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___99_981.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___99_981.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___99_981.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___99_981.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___99_981.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___99_981.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___99_981.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___99_981.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___99_981.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___99_981.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___99_981.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___99_981.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___99_981.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___99_981.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___99_981.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___99_981.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___99_981.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___99_981.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___99_981.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___99_981.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___99_981.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___99_981.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___99_981.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___99_981.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___99_981.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___99_981.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___99_981.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___99_981.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___99_981.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___99_981.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___99_981.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___99_981.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___99_981.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____983 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____983 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____1074 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1115 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
let (extend_wl :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      FStar_TypeChecker_Common.implicits -> worklist)
  =
  fun wl  ->
    fun defer_to_tac  ->
      fun imps  ->
        let uu___108_1152 = wl  in
        let uu____1153 =
          let uu____1163 = as_wl_deferred wl defer_to_tac  in
          FStar_List.append wl.wl_deferred_to_tac uu____1163  in
        {
          attempting = (uu___108_1152.attempting);
          wl_deferred = (uu___108_1152.wl_deferred);
          wl_deferred_to_tac = uu____1153;
          ctr = (uu___108_1152.ctr);
          defer_ok = (uu___108_1152.defer_ok);
          smt_ok = (uu___108_1152.smt_ok);
          umax_heuristic_ok = (uu___108_1152.umax_heuristic_ok);
          tcenv = (uu___108_1152.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps)
        }
  
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____1189 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1200 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1211 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_1229  ->
    match uu___0_1229 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1241 = FStar_Syntax_Util.head_and_args t  in
    match uu____1241 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1304 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1306 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1321 =
                     let uu____1323 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1323  in
                   FStar_Util.format1 "@<%s>" uu____1321
                in
             let uu____1327 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1304 uu____1306 uu____1327
         | uu____1330 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_1342  ->
      match uu___1_1342 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1347 =
            let uu____1351 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1353 =
              let uu____1357 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1359 =
                let uu____1363 =
                  let uu____1367 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1367]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1363
                 in
              uu____1357 :: uu____1359  in
            uu____1351 :: uu____1353  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1347
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1378 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1380 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1382 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1378 uu____1380
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1382
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1396  ->
      match uu___2_1396 with
      | UNIV (u,t) ->
          let x =
            let uu____1402 = FStar_Options.hide_uvar_nums ()  in
            if uu____1402
            then "?"
            else
              (let uu____1409 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1409 FStar_Util.string_of_int)
             in
          let uu____1413 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1413
      | TERM (u,t) ->
          let x =
            let uu____1420 = FStar_Options.hide_uvar_nums ()  in
            if uu____1420
            then "?"
            else
              (let uu____1427 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1427 FStar_Util.string_of_int)
             in
          let uu____1431 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1431
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1450 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1450 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1471 =
      let uu____1475 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1475
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1471 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1494 .
    (FStar_Syntax_Syntax.term * 'Auu____1494) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1513 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1534  ->
              match uu____1534 with
              | (x,uu____1541) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1513 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      wl_deferred_to_tac = [];
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
        (let uu____1588 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1588
         then
           let uu____1593 = FStar_Thunk.force reason  in
           let uu____1596 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1593 uu____1596
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1619 = mklstr (fun uu____1622  -> reason)  in
        giveup env uu____1619 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1628  ->
    match uu___3_1628 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1634 .
    'Auu____1634 FStar_TypeChecker_Common.problem ->
      'Auu____1634 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___168_1646 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___168_1646.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___168_1646.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___168_1646.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___168_1646.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___168_1646.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___168_1646.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___168_1646.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1654 .
    'Auu____1654 FStar_TypeChecker_Common.problem ->
      'Auu____1654 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1674  ->
    match uu___4_1674 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1680  -> FStar_TypeChecker_Common.TProb _1680)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1686  -> FStar_TypeChecker_Common.CProb _1686)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1692  ->
    match uu___5_1692 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___180_1698 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___180_1698.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___180_1698.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___180_1698.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___180_1698.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___180_1698.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___180_1698.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___180_1698.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___180_1698.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___180_1698.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___184_1706 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___184_1706.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___184_1706.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___184_1706.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___184_1706.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___184_1706.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___184_1706.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___184_1706.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___184_1706.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___184_1706.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1719  ->
      match uu___6_1719 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1726  ->
    match uu___7_1726 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1739  ->
    match uu___8_1739 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1754  ->
    match uu___9_1754 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1769  ->
    match uu___10_1769 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1783  ->
    match uu___11_1783 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1797  ->
    match uu___12_1797 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1809  ->
    match uu___13_1809 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1825 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1825) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1855 =
          let uu____1857 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1857  in
        if uu____1855
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1894)::bs ->
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
          let uu____1941 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1965 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1965]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1941
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1993 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____2017 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____2017]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1993
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____2064 =
          let uu____2066 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2066  in
        if uu____2064
        then ()
        else
          (let uu____2071 =
             let uu____2074 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____2074
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____2071 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____2123 =
          let uu____2125 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2125  in
        if uu____2123
        then ()
        else
          (let uu____2130 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____2130)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____2150 =
        let uu____2152 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____2152  in
      if uu____2150
      then ()
      else
        (let msgf m =
           let uu____2166 =
             let uu____2168 =
               let uu____2170 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____2170 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____2168  in
           Prims.op_Hat msg uu____2166  in
         (let uu____2175 = msgf "scope"  in
          let uu____2178 = p_scope prob  in
          def_scope_wf uu____2175 (p_loc prob) uu____2178);
         (let uu____2190 = msgf "guard"  in
          def_check_scoped uu____2190 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____2197 = msgf "lhs"  in
                def_check_scoped uu____2197 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2200 = msgf "rhs"  in
                def_check_scoped uu____2200 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____2207 = msgf "lhs"  in
                def_check_scoped_comp uu____2207 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2210 = msgf "rhs"  in
                def_check_scoped_comp uu____2210 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___277_2231 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___277_2231.wl_deferred);
          wl_deferred_to_tac = (uu___277_2231.wl_deferred_to_tac);
          ctr = (uu___277_2231.ctr);
          defer_ok = (uu___277_2231.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___277_2231.umax_heuristic_ok);
          tcenv = (uu___277_2231.tcenv);
          wl_implicits = (uu___277_2231.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____2239 .
    FStar_TypeChecker_Env.env ->
      ('Auu____2239 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___281_2262 = empty_worklist env  in
      let uu____2263 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____2263;
        wl_deferred = (uu___281_2262.wl_deferred);
        wl_deferred_to_tac = (uu___281_2262.wl_deferred_to_tac);
        ctr = (uu___281_2262.ctr);
        defer_ok = (uu___281_2262.defer_ok);
        smt_ok = (uu___281_2262.smt_ok);
        umax_heuristic_ok = (uu___281_2262.umax_heuristic_ok);
        tcenv = (uu___281_2262.tcenv);
        wl_implicits = (uu___281_2262.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___286_2284 = wl  in
        {
          attempting = (uu___286_2284.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___286_2284.wl_deferred_to_tac);
          ctr = (uu___286_2284.ctr);
          defer_ok = (uu___286_2284.defer_ok);
          smt_ok = (uu___286_2284.smt_ok);
          umax_heuristic_ok = (uu___286_2284.umax_heuristic_ok);
          tcenv = (uu___286_2284.tcenv);
          wl_implicits = (uu___286_2284.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____2311 = FStar_Thunk.mkv reason  in defer uu____2311 prob wl
  
let (find_user_tac_for_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun u  ->
      match u.FStar_Syntax_Syntax.ctx_uvar_meta with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
          a) ->
          let hooks =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          FStar_All.pipe_right hooks
            (FStar_Util.try_find
               (fun hook  ->
                  FStar_All.pipe_right hook.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some (FStar_Syntax_Util.attr_eq a))))
      | uu____2343 -> FStar_Pervasives_Native.None
  
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env  ->
    fun u  ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (let uu____2363 = find_user_tac_for_uvar env u  in
         FStar_Option.isSome uu____2363)
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___305_2383 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___305_2383.wl_deferred);
         wl_deferred_to_tac = (uu___305_2383.wl_deferred_to_tac);
         ctr = (uu___305_2383.ctr);
         defer_ok = (uu___305_2383.defer_ok);
         smt_ok = (uu___305_2383.smt_ok);
         umax_heuristic_ok = (uu___305_2383.umax_heuristic_ok);
         tcenv = (uu___305_2383.tcenv);
         wl_implicits = (uu___305_2383.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____2397 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2397 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2431 = FStar_Syntax_Util.type_u ()  in
            match uu____2431 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2443 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2443 with
                 | (uu____2455,tt,wl1) ->
                     let uu____2458 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2458, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2464  ->
    match uu___14_2464 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2470  -> FStar_TypeChecker_Common.TProb _2470) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2476  -> FStar_TypeChecker_Common.CProb _2476) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2484 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2484 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2504  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2546 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2546 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2546 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2546 FStar_TypeChecker_Common.problem *
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
                        let uu____2633 =
                          let uu____2642 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2642]  in
                        FStar_List.append scope uu____2633
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2685 =
                      let uu____2688 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2688  in
                    FStar_List.append uu____2685
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2707 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2707 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2727 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2727;
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
                  (let uu____2801 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2801 with
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
                  (let uu____2889 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2889 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2927 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2927 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2927 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2927 FStar_TypeChecker_Common.problem *
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
                          let uu____2995 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2995]  in
                        let uu____3014 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____3014
                     in
                  let uu____3017 =
                    let uu____3024 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___388_3035 = wl  in
                       {
                         attempting = (uu___388_3035.attempting);
                         wl_deferred = (uu___388_3035.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___388_3035.wl_deferred_to_tac);
                         ctr = (uu___388_3035.ctr);
                         defer_ok = (uu___388_3035.defer_ok);
                         smt_ok = (uu___388_3035.smt_ok);
                         umax_heuristic_ok =
                           (uu___388_3035.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___388_3035.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____3024
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____3017 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3047 =
                              let uu____3052 =
                                let uu____3053 =
                                  let uu____3062 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____3062
                                   in
                                [uu____3053]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____3052  in
                            uu____3047 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____3090 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3090;
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
                let uu____3138 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3138;
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
  'Auu____3153 .
    worklist ->
      'Auu____3153 FStar_TypeChecker_Common.problem ->
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
              let uu____3186 =
                let uu____3189 =
                  let uu____3190 =
                    let uu____3197 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3197)  in
                  FStar_Syntax_Syntax.NT uu____3190  in
                [uu____3189]  in
              FStar_Syntax_Subst.subst uu____3186 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3219 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3219
        then
          let uu____3227 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3230 = prob_to_string env d  in
          let uu____3232 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3239 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3227 uu____3230 uu____3232 uu____3239
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3251 -> failwith "impossible"  in
           let uu____3254 =
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
           match uu____3254 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3297  ->
            match uu___15_3297 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3309 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3313 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3313 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3344  ->
           match uu___16_3344 with
           | UNIV uu____3347 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3354 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3354
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
        (fun uu___17_3382  ->
           match uu___17_3382 with
           | UNIV (u',t) ->
               let uu____3387 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3387
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3394 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3406 =
        let uu____3407 =
          let uu____3408 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3408
           in
        FStar_Syntax_Subst.compress uu____3407  in
      FStar_All.pipe_right uu____3406 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3420 =
        let uu____3421 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3421  in
      FStar_All.pipe_right uu____3420 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3433 =
        let uu____3437 =
          let uu____3439 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3439  in
        FStar_Pervasives_Native.Some uu____3437  in
      FStar_Profiling.profile (fun uu____3442  -> sn' env t) uu____3433
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
          let uu____3467 =
            let uu____3471 =
              let uu____3473 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3473  in
            FStar_Pervasives_Native.Some uu____3471  in
          FStar_Profiling.profile
            (fun uu____3476  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3467
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3484 = FStar_Syntax_Util.head_and_args t  in
    match uu____3484 with
    | (h,uu____3503) ->
        let uu____3528 =
          let uu____3529 = FStar_Syntax_Subst.compress h  in
          uu____3529.FStar_Syntax_Syntax.n  in
        (match uu____3528 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3534 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3547 =
        let uu____3551 =
          let uu____3553 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3553  in
        FStar_Pervasives_Native.Some uu____3551  in
      FStar_Profiling.profile
        (fun uu____3558  ->
           let uu____3559 = should_strongly_reduce t  in
           if uu____3559
           then
             let uu____3562 =
               let uu____3563 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3563  in
             FStar_All.pipe_right uu____3562 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3547 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3574 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3574) ->
        (FStar_Syntax_Syntax.term * 'Auu____3574)
  =
  fun env  ->
    fun t  ->
      let uu____3597 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3597, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3649  ->
              match uu____3649 with
              | (x,imp) ->
                  let uu____3668 =
                    let uu___494_3669 = x  in
                    let uu____3670 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___494_3669.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___494_3669.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3670
                    }  in
                  (uu____3668, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3694 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3694
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3698 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3698
        | uu____3701 -> u2  in
      let uu____3702 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3702
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3719 =
          let uu____3723 =
            let uu____3725 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3725  in
          FStar_Pervasives_Native.Some uu____3723  in
        FStar_Profiling.profile
          (fun uu____3728  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3719 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3850 = norm_refinement env t12  in
                 match uu____3850 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3865;
                     FStar_Syntax_Syntax.vars = uu____3866;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3890 =
                       let uu____3892 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3894 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3892 uu____3894
                        in
                     failwith uu____3890)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3910 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3910
          | FStar_Syntax_Syntax.Tm_uinst uu____3911 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3948 =
                   let uu____3949 = FStar_Syntax_Subst.compress t1'  in
                   uu____3949.FStar_Syntax_Syntax.n  in
                 match uu____3948 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3964 -> aux true t1'
                 | uu____3972 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3987 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4018 =
                   let uu____4019 = FStar_Syntax_Subst.compress t1'  in
                   uu____4019.FStar_Syntax_Syntax.n  in
                 match uu____4018 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4034 -> aux true t1'
                 | uu____4042 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4057 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4104 =
                   let uu____4105 = FStar_Syntax_Subst.compress t1'  in
                   uu____4105.FStar_Syntax_Syntax.n  in
                 match uu____4104 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4120 -> aux true t1'
                 | uu____4128 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4143 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4158 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4173 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4188 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4203 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4232 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4265 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4286 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4313 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4341 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4378 ->
              let uu____4385 =
                let uu____4387 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4389 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4387 uu____4389
                 in
              failwith uu____4385
          | FStar_Syntax_Syntax.Tm_ascribed uu____4404 ->
              let uu____4431 =
                let uu____4433 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4435 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4433 uu____4435
                 in
              failwith uu____4431
          | FStar_Syntax_Syntax.Tm_delayed uu____4450 ->
              let uu____4465 =
                let uu____4467 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4469 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4467 uu____4469
                 in
              failwith uu____4465
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4484 =
                let uu____4486 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4488 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4486 uu____4488
                 in
              failwith uu____4484
           in
        let uu____4503 = whnf env t1  in aux false uu____4503
  
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
      let uu____4548 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4548 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4589 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4589, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4616 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4616 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4676  ->
    match uu____4676 with
    | (t_base,refopt) ->
        let uu____4707 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4707 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4749 =
      let uu____4753 =
        let uu____4756 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4781  ->
                  match uu____4781 with | (uu____4789,uu____4790,x) -> x))
           in
        FStar_List.append wl.attempting uu____4756  in
      FStar_List.map (wl_prob_to_string wl) uu____4753  in
    FStar_All.pipe_right uu____4749 (FStar_String.concat "\n\t")
  
type flex_t =
  | Flex of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
  FStar_Syntax_Syntax.args) 
let (uu___is_Flex : flex_t -> Prims.bool) = fun projectee  -> true 
let (__proj__Flex__item___0 :
  flex_t ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
      FStar_Syntax_Syntax.args))
  = fun projectee  -> match projectee with | Flex _0 -> _0 
let (flex_reason : flex_t -> Prims.string) =
  fun uu____4850  ->
    match uu____4850 with
    | Flex (uu____4852,u,uu____4854) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4861  ->
    match uu____4861 with
    | Flex (uu____4863,c,args) ->
        let uu____4866 = print_ctx_uvar c  in
        let uu____4868 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4866 uu____4868
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4878 = FStar_Syntax_Util.head_and_args t  in
    match uu____4878 with
    | (head1,_args) ->
        let uu____4922 =
          let uu____4923 = FStar_Syntax_Subst.compress head1  in
          uu____4923.FStar_Syntax_Syntax.n  in
        (match uu____4922 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4927 -> true
         | uu____4941 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4949 = FStar_Syntax_Util.head_and_args t  in
    match uu____4949 with
    | (head1,_args) ->
        let uu____4992 =
          let uu____4993 = FStar_Syntax_Subst.compress head1  in
          uu____4993.FStar_Syntax_Syntax.n  in
        (match uu____4992 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4997) -> u
         | uu____5014 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____5039 = FStar_Syntax_Util.head_and_args t  in
      match uu____5039 with
      | (head1,args) ->
          let uu____5086 =
            let uu____5087 = FStar_Syntax_Subst.compress head1  in
            uu____5087.FStar_Syntax_Syntax.n  in
          (match uu____5086 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5095)) ->
               ((Flex (t, uv, args)), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5128 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_5153  ->
                         match uu___18_5153 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____5158 =
                               let uu____5159 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____5159.FStar_Syntax_Syntax.n  in
                             (match uu____5158 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____5164 -> false)
                         | uu____5166 -> true))
                  in
               (match uu____5128 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____5191 =
                        FStar_List.collect
                          (fun uu___19_5203  ->
                             match uu___19_5203 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____5207 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____5207]
                             | uu____5208 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____5191 FStar_List.rev  in
                    let uu____5231 =
                      let uu____5238 =
                        let uu____5247 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_5269  ->
                                  match uu___20_5269 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____5273 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____5273]
                                  | uu____5274 -> []))
                           in
                        FStar_All.pipe_right uu____5247 FStar_List.rev  in
                      let uu____5297 =
                        let uu____5300 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____5300  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____5238 uu____5297
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____5231 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____5336  ->
                                match uu____5336 with
                                | (x,i) ->
                                    let uu____5355 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____5355, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____5386  ->
                                match uu____5386 with
                                | (a,i) ->
                                    let uu____5405 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____5405, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((Flex (t1, v1, all_args)), wl1))))
           | uu____5427 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5449 =
          let uu____5472 =
            let uu____5473 = FStar_Syntax_Subst.compress k  in
            uu____5473.FStar_Syntax_Syntax.n  in
          match uu____5472 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5555 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5555)
              else
                (let uu____5590 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5590 with
                 | (ys',t1,uu____5623) ->
                     let uu____5628 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5628))
          | uu____5667 ->
              let uu____5668 =
                let uu____5673 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5673)  in
              ((ys, t), uu____5668)
           in
        match uu____5449 with
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
                 let uu____5768 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5768 c  in
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
               (let uu____5846 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5846
                then
                  let uu____5851 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5853 = print_ctx_uvar uv  in
                  let uu____5855 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5851 uu____5853 uu____5855
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5864 =
                   let uu____5866 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5866  in
                 let uu____5869 =
                   let uu____5872 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5872
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5864 uu____5869 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5905 =
               let uu____5906 =
                 let uu____5908 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5910 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5908 uu____5910
                  in
               failwith uu____5906  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5976  ->
                       match uu____5976 with
                       | (a,i) ->
                           let uu____5997 =
                             let uu____5998 = FStar_Syntax_Subst.compress a
                                in
                             uu____5998.FStar_Syntax_Syntax.n  in
                           (match uu____5997 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____6024 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____6034 =
                 let uu____6036 = is_flex g  in Prims.op_Negation uu____6036
                  in
               if uu____6034
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____6045 = destruct_flex_t g wl  in
                  match uu____6045 with
                  | (Flex (uu____6050,uv1,args),wl1) ->
                      ((let uu____6055 = args_as_binders args  in
                        assign_solution uu____6055 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___756_6057 = wl1  in
              {
                attempting = (uu___756_6057.attempting);
                wl_deferred = (uu___756_6057.wl_deferred);
                wl_deferred_to_tac = (uu___756_6057.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___756_6057.defer_ok);
                smt_ok = (uu___756_6057.smt_ok);
                umax_heuristic_ok = (uu___756_6057.umax_heuristic_ok);
                tcenv = (uu___756_6057.tcenv);
                wl_implicits = (uu___756_6057.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6082 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6082
         then
           let uu____6087 = FStar_Util.string_of_int pid  in
           let uu____6089 =
             let uu____6091 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____6091 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6087 uu____6089
         else ());
        commit sol;
        (let uu___764_6105 = wl  in
         {
           attempting = (uu___764_6105.attempting);
           wl_deferred = (uu___764_6105.wl_deferred);
           wl_deferred_to_tac = (uu___764_6105.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___764_6105.defer_ok);
           smt_ok = (uu___764_6105.smt_ok);
           umax_heuristic_ok = (uu___764_6105.umax_heuristic_ok);
           tcenv = (uu___764_6105.tcenv);
           wl_implicits = (uu___764_6105.wl_implicits)
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
          (let uu____6141 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6141
           then
             let uu____6146 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6150 =
               let uu____6152 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____6152 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6146 uu____6150
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
        let uu____6187 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6187 FStar_Util.set_elements  in
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
      let uu____6227 = occurs uk t  in
      match uu____6227 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6266 =
                 let uu____6268 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6270 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6268 uu____6270
                  in
               FStar_Pervasives_Native.Some uu____6266)
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
            let uu____6390 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6390 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6441 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6498  ->
             match uu____6498 with
             | (x,uu____6510) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6528 = FStar_List.last bs  in
      match uu____6528 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6552) ->
          let uu____6563 =
            FStar_Util.prefix_until
              (fun uu___21_6578  ->
                 match uu___21_6578 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6581 -> false) g
             in
          (match uu____6563 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6595,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6632 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6632 with
        | (pfx,uu____6642) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6654 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6654 with
             | (uu____6662,src',wl1) ->
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
                 | uu____6776 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6777 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6841  ->
                  fun uu____6842  ->
                    match (uu____6841, uu____6842) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6945 =
                          let uu____6947 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6947
                           in
                        if uu____6945
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6981 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6981
                           then
                             let uu____6998 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6998)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6777 with | (isect,uu____7048) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____7084 'Auu____7085 .
    (FStar_Syntax_Syntax.bv * 'Auu____7084) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____7085) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7143  ->
              fun uu____7144  ->
                match (uu____7143, uu____7144) with
                | ((a,uu____7163),(b,uu____7165)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____7181 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____7181) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7212  ->
           match uu____7212 with
           | (y,uu____7219) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____7229 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____7229) Prims.list ->
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
                   let uu____7391 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7391
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7424 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7476 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7520 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7541 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7549  ->
    match uu___22_7549 with
    | MisMatch (d1,d2) ->
        let uu____7561 =
          let uu____7563 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7565 =
            let uu____7567 =
              let uu____7569 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7569 ")"  in
            Prims.op_Hat ") (" uu____7567  in
          Prims.op_Hat uu____7563 uu____7565  in
        Prims.op_Hat "MisMatch (" uu____7561
    | HeadMatch u ->
        let uu____7576 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7576
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7585  ->
    match uu___23_7585 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7602 -> HeadMatch false
  
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
          let uu____7624 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7624 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7635 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7659 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7669 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7688 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7688
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7689 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7690 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7691 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7704 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7718 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7742) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7748,uu____7749) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7791) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7816;
             FStar_Syntax_Syntax.index = uu____7817;
             FStar_Syntax_Syntax.sort = t2;_},uu____7819)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7827 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7828 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7829 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7844 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7851 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7871 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7871
  
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
           { FStar_Syntax_Syntax.blob = uu____7890;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7891;
             FStar_Syntax_Syntax.ltyp = uu____7892;
             FStar_Syntax_Syntax.rng = uu____7893;_},uu____7894)
            ->
            let uu____7905 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7905 t21
        | (uu____7906,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7907;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7908;
             FStar_Syntax_Syntax.ltyp = uu____7909;
             FStar_Syntax_Syntax.rng = uu____7910;_})
            ->
            let uu____7921 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7921
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7933 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7933
            then FullMatch
            else
              (let uu____7938 =
                 let uu____7947 =
                   let uu____7950 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7950  in
                 let uu____7951 =
                   let uu____7954 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7954  in
                 (uu____7947, uu____7951)  in
               MisMatch uu____7938)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7960),FStar_Syntax_Syntax.Tm_uinst (g,uu____7962)) ->
            let uu____7971 = head_matches env f g  in
            FStar_All.pipe_right uu____7971 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7972) -> HeadMatch true
        | (uu____7974,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7978 = FStar_Const.eq_const c d  in
            if uu____7978
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7988),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7990)) ->
            let uu____8023 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____8023
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____8033),FStar_Syntax_Syntax.Tm_refine (y,uu____8035)) ->
            let uu____8044 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8044 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8046),uu____8047) ->
            let uu____8052 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8052 head_match
        | (uu____8053,FStar_Syntax_Syntax.Tm_refine (x,uu____8055)) ->
            let uu____8060 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8060 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8061,FStar_Syntax_Syntax.Tm_type
           uu____8062) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8064,FStar_Syntax_Syntax.Tm_arrow uu____8065) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____8096),FStar_Syntax_Syntax.Tm_app (head',uu____8098))
            ->
            let uu____8147 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____8147 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____8149),uu____8150) ->
            let uu____8175 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____8175 head_match
        | (uu____8176,FStar_Syntax_Syntax.Tm_app (head1,uu____8178)) ->
            let uu____8203 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____8203 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8204,FStar_Syntax_Syntax.Tm_let
           uu____8205) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8233,FStar_Syntax_Syntax.Tm_match uu____8234) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8280,FStar_Syntax_Syntax.Tm_abs
           uu____8281) -> HeadMatch true
        | uu____8319 ->
            let uu____8324 =
              let uu____8333 = delta_depth_of_term env t11  in
              let uu____8336 = delta_depth_of_term env t21  in
              (uu____8333, uu____8336)  in
            MisMatch uu____8324
  
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
              let uu____8405 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8405  in
            (let uu____8407 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8407
             then
               let uu____8412 = FStar_Syntax_Print.term_to_string t  in
               let uu____8414 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8412 uu____8414
             else ());
            (let uu____8419 =
               let uu____8420 = FStar_Syntax_Util.un_uinst head1  in
               uu____8420.FStar_Syntax_Syntax.n  in
             match uu____8419 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8426 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8426 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8440 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8440
                        then
                          let uu____8445 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8445
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8450 ->
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
                      let uu____8468 =
                        let uu____8470 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8470 = FStar_Syntax_Util.Equal  in
                      if uu____8468
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8477 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8477
                          then
                            let uu____8482 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8484 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8482
                              uu____8484
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8489 -> FStar_Pervasives_Native.None)
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
            (let uu____8641 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8641
             then
               let uu____8646 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8648 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8650 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8646
                 uu____8648 uu____8650
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8678 =
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
               match uu____8678 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8726 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8726 with
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
                  uu____8764),uu____8765)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8786 =
                      let uu____8795 = maybe_inline t11  in
                      let uu____8798 = maybe_inline t21  in
                      (uu____8795, uu____8798)  in
                    match uu____8786 with
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
                 (uu____8841,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8842))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8863 =
                      let uu____8872 = maybe_inline t11  in
                      let uu____8875 = maybe_inline t21  in
                      (uu____8872, uu____8875)  in
                    match uu____8863 with
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
             | MisMatch uu____8930 -> fail1 n_delta r t11 t21
             | uu____8939 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8954 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8954
           then
             let uu____8959 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8961 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8963 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8971 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8988 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8988
                    (fun uu____9023  ->
                       match uu____9023 with
                       | (t11,t21) ->
                           let uu____9031 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____9033 =
                             let uu____9035 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____9035  in
                           Prims.op_Hat uu____9031 uu____9033))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8959 uu____8961 uu____8963 uu____8971
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9052 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9052 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_9067  ->
    match uu___24_9067 with
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
      let uu___1253_9116 = p  in
      let uu____9119 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9120 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1253_9116.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9119;
        FStar_TypeChecker_Common.relation =
          (uu___1253_9116.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9120;
        FStar_TypeChecker_Common.element =
          (uu___1253_9116.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1253_9116.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1253_9116.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1253_9116.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1253_9116.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1253_9116.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9135 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9135
            (fun _9140  -> FStar_TypeChecker_Common.TProb _9140)
      | FStar_TypeChecker_Common.CProb uu____9141 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9164 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9164 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9172 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9172 with
           | (lh,lhs_args) ->
               let uu____9219 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9219 with
                | (rh,rhs_args) ->
                    let uu____9266 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9279,FStar_Syntax_Syntax.Tm_uvar uu____9280)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9369 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9396,uu____9397)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9412,FStar_Syntax_Syntax.Tm_uvar uu____9413)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9428,FStar_Syntax_Syntax.Tm_arrow uu____9429)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1304_9459 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1304_9459.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1304_9459.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1304_9459.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1304_9459.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1304_9459.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1304_9459.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1304_9459.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1304_9459.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1304_9459.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9462,FStar_Syntax_Syntax.Tm_type uu____9463)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1304_9479 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1304_9479.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1304_9479.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1304_9479.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1304_9479.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1304_9479.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1304_9479.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1304_9479.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1304_9479.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1304_9479.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9482,FStar_Syntax_Syntax.Tm_uvar uu____9483)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1304_9499 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1304_9499.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1304_9499.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1304_9499.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1304_9499.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1304_9499.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1304_9499.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1304_9499.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1304_9499.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1304_9499.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9502,FStar_Syntax_Syntax.Tm_uvar uu____9503)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9518,uu____9519)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9534,FStar_Syntax_Syntax.Tm_uvar uu____9535)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9550,uu____9551) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9266 with
                     | (rank,tp1) ->
                         let uu____9564 =
                           FStar_All.pipe_right
                             (let uu___1324_9568 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1324_9568.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1324_9568.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1324_9568.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1324_9568.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1324_9568.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1324_9568.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1324_9568.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1324_9568.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1324_9568.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9571  ->
                                FStar_TypeChecker_Common.TProb _9571)
                            in
                         (rank, uu____9564))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9575 =
            FStar_All.pipe_right
              (let uu___1328_9579 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1328_9579.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1328_9579.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1328_9579.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1328_9579.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1328_9579.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1328_9579.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1328_9579.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1328_9579.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1328_9579.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9582  -> FStar_TypeChecker_Common.CProb _9582)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9575)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9642 probs =
      match uu____9642 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9723 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9744 = rank wl.tcenv hd1  in
               (match uu____9744 with
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
                      (let uu____9805 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9810 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9810)
                          in
                       if uu____9805
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
          let uu____9883 = FStar_Syntax_Util.head_and_args t  in
          match uu____9883 with
          | (hd1,uu____9902) ->
              let uu____9927 =
                let uu____9928 = FStar_Syntax_Subst.compress hd1  in
                uu____9928.FStar_Syntax_Syntax.n  in
              (match uu____9927 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9933) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9968  ->
                           match uu____9968 with
                           | (y,uu____9977) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10000  ->
                                       match uu____10000 with
                                       | (x,uu____10009) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10014 -> false)
           in
        let uu____10016 = rank tcenv p  in
        match uu____10016 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10025 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10106 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10125 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10144 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10161 = FStar_Thunk.mkv s  in UFailed uu____10161 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10176 = mklstr s  in UFailed uu____10176 
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
                        let uu____10227 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10227 with
                        | (k,uu____10235) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10248 -> false)))
            | uu____10250 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10302 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____10310 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____10310 = Prims.int_zero))
                           in
                        if uu____10302 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____10331 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____10339 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____10339 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____10331)
               in
            let uu____10343 = filter1 u12  in
            let uu____10346 = filter1 u22  in (uu____10343, uu____10346)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10381 = filter_out_common_univs us1 us2  in
                   (match uu____10381 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10441 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10441 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10444 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10461  ->
                               let uu____10462 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10464 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10462 uu____10464))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10490 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10490 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10516 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10516 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10519 ->
                   ufailed_thunk
                     (fun uu____10530  ->
                        let uu____10531 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10533 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10531 uu____10533 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10536,uu____10537) ->
              let uu____10539 =
                let uu____10541 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10543 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10541 uu____10543
                 in
              failwith uu____10539
          | (FStar_Syntax_Syntax.U_unknown ,uu____10546) ->
              let uu____10547 =
                let uu____10549 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10551 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10549 uu____10551
                 in
              failwith uu____10547
          | (uu____10554,FStar_Syntax_Syntax.U_bvar uu____10555) ->
              let uu____10557 =
                let uu____10559 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10561 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10559 uu____10561
                 in
              failwith uu____10557
          | (uu____10564,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10565 =
                let uu____10567 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10569 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10567 uu____10569
                 in
              failwith uu____10565
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10599 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10599
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10616 = occurs_univ v1 u3  in
              if uu____10616
              then
                let uu____10619 =
                  let uu____10621 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10623 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10621 uu____10623
                   in
                try_umax_components u11 u21 uu____10619
              else
                (let uu____10628 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10628)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10640 = occurs_univ v1 u3  in
              if uu____10640
              then
                let uu____10643 =
                  let uu____10645 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10647 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10645 uu____10647
                   in
                try_umax_components u11 u21 uu____10643
              else
                (let uu____10652 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10652)
          | (FStar_Syntax_Syntax.U_max uu____10653,uu____10654) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10662 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10662
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10668,FStar_Syntax_Syntax.U_max uu____10669) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10677 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10677
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10683,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10685,FStar_Syntax_Syntax.U_name uu____10686) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10688) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10690) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10692,FStar_Syntax_Syntax.U_succ uu____10693) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10695,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10802 = bc1  in
      match uu____10802 with
      | (bs1,mk_cod1) ->
          let uu____10846 = bc2  in
          (match uu____10846 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10957 = aux xs ys  in
                     (match uu____10957 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11040 =
                       let uu____11047 = mk_cod1 xs  in ([], uu____11047)  in
                     let uu____11050 =
                       let uu____11057 = mk_cod2 ys  in ([], uu____11057)  in
                     (uu____11040, uu____11050)
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
                  let uu____11126 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11126 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11129 =
                    let uu____11130 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11130 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11129
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11135 = has_type_guard t1 t2  in (uu____11135, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11136 = has_type_guard t2 t1  in (uu____11136, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___25_11143  ->
    match uu___25_11143 with
    | Flex (uu____11145,uu____11146,[]) -> true
    | uu____11156 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11170 = f  in
      match uu____11170 with
      | Flex (uu____11172,u,uu____11174) ->
          should_defer_uvar_to_user_tac wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11198 = f  in
      match uu____11198 with
      | Flex
          (uu____11205,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11206;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11207;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11210;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11211;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11212;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11213;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11277  ->
                 match uu____11277 with
                 | (y,uu____11286) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11440 =
                  let uu____11455 =
                    let uu____11458 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11458  in
                  ((FStar_List.rev pat_binders), uu____11455)  in
                FStar_Pervasives_Native.Some uu____11440
            | (uu____11491,[]) ->
                let uu____11522 =
                  let uu____11537 =
                    let uu____11540 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11540  in
                  ((FStar_List.rev pat_binders), uu____11537)  in
                FStar_Pervasives_Native.Some uu____11522
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11631 =
                  let uu____11632 = FStar_Syntax_Subst.compress a  in
                  uu____11632.FStar_Syntax_Syntax.n  in
                (match uu____11631 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11652 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11652
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1665_11682 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1665_11682.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1665_11682.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11686 =
                            let uu____11687 =
                              let uu____11694 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11694)  in
                            FStar_Syntax_Syntax.NT uu____11687  in
                          [uu____11686]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1671_11710 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_11710.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_11710.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11711 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11751 =
                  let uu____11758 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11758  in
                (match uu____11751 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11817 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11842 ->
               let uu____11843 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11843 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12175 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12175
       then
         let uu____12180 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12180
       else ());
      (let uu____12186 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12186
       then
         let uu____12191 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12191
       else ());
      (let uu____12196 = next_prob probs  in
       match uu____12196 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1698_12223 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1698_12223.wl_deferred);
               wl_deferred_to_tac = (uu___1698_12223.wl_deferred_to_tac);
               ctr = (uu___1698_12223.ctr);
               defer_ok = (uu___1698_12223.defer_ok);
               smt_ok = (uu___1698_12223.smt_ok);
               umax_heuristic_ok = (uu___1698_12223.umax_heuristic_ok);
               tcenv = (uu___1698_12223.tcenv);
               wl_implicits = (uu___1698_12223.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12232 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12232
                 then
                   let uu____12235 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____12235
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
                       maybe_defer_to_user_tac env tp
                         "deferring flex_rigid or flex_flex subtyping" probs1
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1710_12247 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1710_12247.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1710_12247.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1710_12247.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1710_12247.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1710_12247.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1710_12247.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1710_12247.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1710_12247.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1710_12247.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12267 =
                  let uu____12274 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12274, (probs.wl_implicits))  in
                Success uu____12267
            | uu____12280 ->
                let uu____12290 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12355  ->
                          match uu____12355 with
                          | (c,uu____12365,uu____12366) -> c < probs.ctr))
                   in
                (match uu____12290 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12414 =
                            let uu____12421 = as_deferred probs.wl_deferred
                               in
                            let uu____12422 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12421, uu____12422, (probs.wl_implicits))
                             in
                          Success uu____12414
                      | uu____12423 ->
                          let uu____12433 =
                            let uu___1724_12434 = probs  in
                            let uu____12435 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12456  ->
                                      match uu____12456 with
                                      | (uu____12464,uu____12465,y) -> y))
                               in
                            {
                              attempting = uu____12435;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1724_12434.wl_deferred_to_tac);
                              ctr = (uu___1724_12434.ctr);
                              defer_ok = (uu___1724_12434.defer_ok);
                              smt_ok = (uu___1724_12434.smt_ok);
                              umax_heuristic_ok =
                                (uu___1724_12434.umax_heuristic_ok);
                              tcenv = (uu___1724_12434.tcenv);
                              wl_implicits = (uu___1724_12434.wl_implicits)
                            }  in
                          solve env uu____12433))))

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
            let uu____12474 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12474 with
            | USolved wl1 ->
                let uu____12476 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12476
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12479 = defer_lit "" orig wl1  in
                solve env uu____12479

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
                  let uu____12530 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12530 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12533 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12546;
                  FStar_Syntax_Syntax.vars = uu____12547;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12550;
                  FStar_Syntax_Syntax.vars = uu____12551;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12564,uu____12565) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12573,FStar_Syntax_Syntax.Tm_uinst uu____12574) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12582 -> USolved wl

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
            ((let uu____12593 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12593
              then
                let uu____12598 = prob_to_string env orig  in
                let uu____12600 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12598 uu____12600
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun reason  ->
        fun wl  ->
          let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl  in
          let wl2 =
            let uu___1806_12615 = wl1  in
            let uu____12616 =
              let uu____12626 =
                let uu____12634 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12634, orig)  in
              uu____12626 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1806_12615.attempting);
              wl_deferred = (uu___1806_12615.wl_deferred);
              wl_deferred_to_tac = uu____12616;
              ctr = (uu___1806_12615.ctr);
              defer_ok = (uu___1806_12615.defer_ok);
              smt_ok = (uu___1806_12615.smt_ok);
              umax_heuristic_ok = (uu___1806_12615.umax_heuristic_ok);
              tcenv = (uu___1806_12615.tcenv);
              wl_implicits = (uu___1806_12615.wl_implicits)
            }  in
          solve env wl2

and (maybe_defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem ->
      Prims.string -> worklist -> solution)
  =
  fun env  ->
    fun prob  ->
      fun reason  ->
        fun wl  ->
          match prob.FStar_TypeChecker_Common.relation with
          | FStar_TypeChecker_Common.EQ  ->
              let should_defer_tac t =
                let uu____12663 = FStar_Syntax_Util.head_and_args t  in
                match uu____12663 with
                | (head1,uu____12687) ->
                    let uu____12712 =
                      let uu____12713 = FStar_Syntax_Subst.compress head1  in
                      uu____12713.FStar_Syntax_Syntax.n  in
                    (match uu____12712 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12723) ->
                         let uu____12740 =
                           should_defer_uvar_to_user_tac wl.tcenv uv  in
                         (uu____12740,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12744 -> (false, ""))
                 in
              let uu____12749 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12749 with
               | (l1,r1) ->
                   let uu____12762 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12762 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12779 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12779)))
          | uu____12780 ->
              let uu____12781 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12781

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
               let uu____12867 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12867 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12922 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12922
                then
                  let uu____12927 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12929 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12927 uu____12929
                else ());
               (let uu____12934 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12934 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12980 = eq_prob t1 t2 wl2  in
                         (match uu____12980 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13001 ->
                         let uu____13010 = eq_prob t1 t2 wl2  in
                         (match uu____13010 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13060 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13075 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13076 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13075, uu____13076)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13081 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13082 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13081, uu____13082)
                            in
                         (match uu____13060 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13113 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13113 with
                                | (t1_hd,t1_args) ->
                                    let uu____13158 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13158 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13224 =
                                              let uu____13231 =
                                                let uu____13242 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13242 :: t1_args  in
                                              let uu____13259 =
                                                let uu____13268 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13268 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13317  ->
                                                   fun uu____13318  ->
                                                     fun uu____13319  ->
                                                       match (uu____13317,
                                                               uu____13318,
                                                               uu____13319)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13369),
                                                          (a2,uu____13371))
                                                           ->
                                                           let uu____13408 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13408
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13231
                                                uu____13259
                                               in
                                            match uu____13224 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1909_13434 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1909_13434.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1909_13434.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1909_13434.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1909_13434.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13445 =
                                                  solve env1 wl'  in
                                                (match uu____13445 with
                                                 | Success
                                                     (uu____13448,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13452 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13452))
                                                 | Failed uu____13453 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13485 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13485 with
                                | (t1_base,p1_opt) ->
                                    let uu____13521 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13521 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13620 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13620
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
                                               let uu____13673 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13673
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
                                               let uu____13705 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13705
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
                                               let uu____13737 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13737
                                           | uu____13740 -> t_base  in
                                         let uu____13757 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13757 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13771 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13771, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13778 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13778 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13814 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13814 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13850 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13850
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
                              let uu____13874 = combine t11 t21 wl2  in
                              (match uu____13874 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13907 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13907
                                     then
                                       let uu____13912 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13912
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13954 ts1 =
               match uu____13954 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14017 = pairwise out t wl2  in
                        (match uu____14017 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14053 =
               let uu____14064 = FStar_List.hd ts  in (uu____14064, [], wl1)
                in
             let uu____14073 = FStar_List.tl ts  in
             aux uu____14053 uu____14073  in
           let uu____14080 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14080 with
           | (this_flex,this_rigid) ->
               let uu____14106 =
                 let uu____14107 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14107.FStar_Syntax_Syntax.n  in
               (match uu____14106 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14132 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14132
                    then
                      let uu____14135 = destruct_flex_t this_flex wl  in
                      (match uu____14135 with
                       | (flex,wl1) ->
                           let uu____14142 = quasi_pattern env flex  in
                           (match uu____14142 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____14161 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14161
                                  then
                                    let uu____14166 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14166
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14173 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2019_14176 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2019_14176.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2019_14176.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2019_14176.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2019_14176.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2019_14176.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2019_14176.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2019_14176.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2019_14176.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2019_14176.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14173)
                | uu____14177 ->
                    ((let uu____14179 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14179
                      then
                        let uu____14184 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14184
                      else ());
                     (let uu____14189 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14189 with
                      | (u,_args) ->
                          let uu____14232 =
                            let uu____14233 = FStar_Syntax_Subst.compress u
                               in
                            uu____14233.FStar_Syntax_Syntax.n  in
                          (match uu____14232 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____14261 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14261 with
                                 | (u',uu____14280) ->
                                     let uu____14305 =
                                       let uu____14306 = whnf env u'  in
                                       uu____14306.FStar_Syntax_Syntax.n  in
                                     (match uu____14305 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14328 -> false)
                                  in
                               let uu____14330 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_14353  ->
                                         match uu___26_14353 with
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
                                              | uu____14367 -> false)
                                         | uu____14371 -> false))
                                  in
                               (match uu____14330 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14386 = whnf env this_rigid
                                         in
                                      let uu____14387 =
                                        FStar_List.collect
                                          (fun uu___27_14393  ->
                                             match uu___27_14393 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14399 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14399]
                                             | uu____14403 -> [])
                                          bounds_probs
                                         in
                                      uu____14386 :: uu____14387  in
                                    let uu____14404 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14404 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14437 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14452 =
                                               let uu____14453 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14453.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14452 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14465 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14465)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14476 -> bound  in
                                           let uu____14477 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14477)  in
                                         (match uu____14437 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14512 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14512
                                                then
                                                  let wl'1 =
                                                    let uu___2079_14518 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2079_14518.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2079_14518.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2079_14518.ctr);
                                                      defer_ok =
                                                        (uu___2079_14518.defer_ok);
                                                      smt_ok =
                                                        (uu___2079_14518.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2079_14518.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2079_14518.tcenv);
                                                      wl_implicits =
                                                        (uu___2079_14518.wl_implicits)
                                                    }  in
                                                  let uu____14519 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14519
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14525 =
                                                  solve_t env eq_prob
                                                    (let uu___2084_14527 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2084_14527.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2084_14527.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2084_14527.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2084_14527.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2084_14527.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2084_14527.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____14525 with
                                                | Success
                                                    (uu____14529,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2091_14533 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2091_14533.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2091_14533.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2091_14533.ctr);
                                                        defer_ok =
                                                          (uu___2091_14533.defer_ok);
                                                        smt_ok =
                                                          (uu___2091_14533.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2091_14533.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2091_14533.tcenv);
                                                        wl_implicits =
                                                          (uu___2091_14533.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      extend_wl wl2
                                                        defer_to_tac imps
                                                       in
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
                                                    let uu____14550 =
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
                                                    ((let uu____14562 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14562
                                                      then
                                                        let uu____14567 =
                                                          let uu____14569 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14569
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14567
                                                      else ());
                                                     (let uu____14582 =
                                                        let uu____14597 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14597)
                                                         in
                                                      match uu____14582 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14619))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14645 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14645
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
                                                                  let uu____14665
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14665))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14690 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14690
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
                                                                    let uu____14710
                                                                    =
                                                                    let uu____14715
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14715
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14710
                                                                    [] wl2
                                                                     in
                                                                  let uu____14721
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14721))))
                                                      | uu____14722 ->
                                                          let uu____14737 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14737 p)))))))
                           | uu____14744 when flip ->
                               let uu____14745 =
                                 let uu____14747 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14749 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14747 uu____14749
                                  in
                               failwith uu____14745
                           | uu____14752 ->
                               let uu____14753 =
                                 let uu____14755 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14757 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14755 uu____14757
                                  in
                               failwith uu____14753)))))

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
                      (fun uu____14793  ->
                         match uu____14793 with
                         | (x,i) ->
                             let uu____14812 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14812, i)) bs_lhs
                     in
                  let uu____14815 = lhs  in
                  match uu____14815 with
                  | Flex (uu____14816,u_lhs,uu____14818) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14915 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14925 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14925, univ)
                             in
                          match uu____14915 with
                          | (k,univ) ->
                              let uu____14932 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14932 with
                               | (uu____14949,u,wl3) ->
                                   let uu____14952 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14952, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14978 =
                              let uu____14991 =
                                let uu____15002 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____15002 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15053  ->
                                   fun uu____15054  ->
                                     match (uu____15053, uu____15054) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15155 =
                                           let uu____15162 =
                                             let uu____15165 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15165
                                              in
                                           copy_uvar u_lhs [] uu____15162 wl2
                                            in
                                         (match uu____15155 with
                                          | (uu____15194,t_a,wl3) ->
                                              let uu____15197 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15197 with
                                               | (uu____15216,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14991
                                ([], wl1)
                               in
                            (match uu____14978 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2204_15272 = ct  in
                                   let uu____15273 =
                                     let uu____15276 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15276
                                      in
                                   let uu____15291 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2204_15272.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2204_15272.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15273;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15291;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2204_15272.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2207_15309 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2207_15309.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2207_15309.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15312 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____15312 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15350 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15350 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15361 =
                                          let uu____15366 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15366)  in
                                        TERM uu____15361  in
                                      let uu____15367 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15367 with
                                       | (sub_prob,wl3) ->
                                           let uu____15381 =
                                             let uu____15382 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15382
                                              in
                                           solve env uu____15381))
                             | (x,imp)::formals2 ->
                                 let uu____15404 =
                                   let uu____15411 =
                                     let uu____15414 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15414
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15411 wl1
                                    in
                                 (match uu____15404 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15435 =
                                          let uu____15438 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15438
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15435 u_x
                                         in
                                      let uu____15439 =
                                        let uu____15442 =
                                          let uu____15445 =
                                            let uu____15446 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15446, imp)  in
                                          [uu____15445]  in
                                        FStar_List.append bs_terms
                                          uu____15442
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15439 formals2 wl2)
                              in
                           let uu____15473 = occurs_check u_lhs arrow1  in
                           (match uu____15473 with
                            | (uu____15486,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15502 =
                                    mklstr
                                      (fun uu____15507  ->
                                         let uu____15508 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15508)
                                     in
                                  giveup_or_defer env orig wl uu____15502
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
              (let uu____15541 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15541
               then
                 let uu____15546 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15549 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15546 (rel_to_string (p_rel orig)) uu____15549
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15680 = rhs wl1 scope env1 subst1  in
                     (match uu____15680 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15703 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15703
                            then
                              let uu____15708 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15708
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15786 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15786 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2277_15788 = hd1  in
                       let uu____15789 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2277_15788.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2277_15788.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15789
                       }  in
                     let hd21 =
                       let uu___2280_15793 = hd2  in
                       let uu____15794 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2280_15793.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2280_15793.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15794
                       }  in
                     let uu____15797 =
                       let uu____15802 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15802
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15797 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15825 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15825
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15832 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15832 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15904 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15904
                                  in
                               ((let uu____15922 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15922
                                 then
                                   let uu____15927 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15929 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15927
                                     uu____15929
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15964 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____16000 = aux wl [] env [] bs1 bs2  in
               match uu____16000 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16059 = attempt sub_probs wl2  in
                   solve env1 uu____16059)

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
            let uu___2318_16079 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2318_16079.wl_deferred_to_tac);
              ctr = (uu___2318_16079.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2318_16079.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16091 = try_solve env wl'  in
          match uu____16091 with
          | Success (uu____16092,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16105 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16105 wl)

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
            let uu____16111 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16111
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16124 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16124 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16158 = lhs1  in
                 match uu____16158 with
                 | Flex (uu____16161,ctx_u,uu____16163) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16171 ->
                           let uu____16172 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16172 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16221 = quasi_pattern env1 lhs1  in
                 match uu____16221 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16255) ->
                     let uu____16260 = lhs1  in
                     (match uu____16260 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16275 = occurs_check ctx_u rhs1  in
                          (match uu____16275 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16326 =
                                   let uu____16334 =
                                     let uu____16336 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16336
                                      in
                                   FStar_Util.Inl uu____16334  in
                                 (uu____16326, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16364 =
                                    let uu____16366 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16366  in
                                  if uu____16364
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16393 =
                                       let uu____16401 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16401  in
                                     let uu____16407 =
                                       restrict_all_uvars ctx_u uvars1 wl1
                                        in
                                     (uu____16393, uu____16407)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16451 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16451 with
                 | (rhs_hd,args) ->
                     let uu____16494 = FStar_Util.prefix args  in
                     (match uu____16494 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              FStar_Pervasives_Native.None
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16566 = lhs1  in
                          (match uu____16566 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16570 =
                                 let uu____16581 =
                                   let uu____16588 =
                                     let uu____16591 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16591
                                      in
                                   copy_uvar u_lhs [] uu____16588 wl1  in
                                 match uu____16581 with
                                 | (uu____16618,t_last_arg,wl2) ->
                                     let uu____16621 =
                                       let uu____16628 =
                                         let uu____16629 =
                                           let uu____16638 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16638]  in
                                         FStar_List.append bs_lhs uu____16629
                                          in
                                       copy_uvar u_lhs uu____16628 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16621 with
                                      | (uu____16673,lhs',wl3) ->
                                          let uu____16676 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16676 with
                                           | (uu____16693,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16570 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16714 =
                                        let uu____16715 =
                                          let uu____16720 =
                                            let uu____16721 =
                                              let uu____16724 =
                                                let uu____16729 =
                                                  let uu____16730 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lhs'_last_arg
                                                     in
                                                  [uu____16730]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  lhs' uu____16729
                                                 in
                                              uu____16724
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16721
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16720)  in
                                        TERM uu____16715  in
                                      [uu____16714]  in
                                    let uu____16755 =
                                      let uu____16762 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16762 with
                                      | (p1,wl3) ->
                                          let uu____16782 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16782 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16755 with
                                     | (sub_probs,wl3) ->
                                         let uu____16814 =
                                           let uu____16815 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16815  in
                                         solve env1 uu____16814))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16849 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16849 with
                   | (uu____16867,args) ->
                       (match args with | [] -> false | uu____16903 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16922 =
                     let uu____16923 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16923.FStar_Syntax_Syntax.n  in
                   match uu____16922 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16927 -> true
                   | uu____16943 -> false  in
                 let uu____16945 = quasi_pattern env1 lhs1  in
                 match uu____16945 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       mklstr
                         (fun uu____16964  ->
                            let uu____16965 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____16965)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____16974 = is_app rhs1  in
                     if uu____16974
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____16979 = is_arrow rhs1  in
                        if uu____16979
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____16992  ->
                                  let uu____16993 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____16993)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____16997 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16997
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____17003 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17003
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____17008 = lhs  in
                   (match uu____17008 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____17012 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____17012 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____17030 =
                                 let uu____17034 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17034
                                  in
                               FStar_All.pipe_right uu____17030
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17055 = occurs_check ctx_uv rhs1  in
                             (match uu____17055 with
                              | (uvars1,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17084 =
                                      let uu____17085 =
                                        let uu____17087 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17087
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17085
                                       in
                                    giveup_or_defer env orig wl uu____17084
                                  else
                                    (let uu____17095 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17095
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars1 wl
                                          in
                                       let uu____17102 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17102
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17118  ->
                                                 let uu____17119 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17121 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17123 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17119 uu____17121
                                                   uu____17123)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17135 ->
                             if wl.defer_ok
                             then
                               let uu____17139 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17139
                             else
                               (let uu____17144 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17144 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17170 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17170
                                | (FStar_Util.Inl msg,uu____17172) ->
                                    first_order orig env wl lhs rhs))))

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
                  let uu____17190 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17190
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17196 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17196
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17201 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17201
                then
                  defer_to_user_tac env orig
                    (Prims.op_Hat (flex_reason lhs)
                       (Prims.op_Hat ", " (flex_reason rhs))) wl
                else
                  if
                    wl.defer_ok &&
                      ((Prims.op_Negation (is_flex_pat lhs)) ||
                         (Prims.op_Negation (is_flex_pat rhs)))
                  then
                    (let uu____17208 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17208)
                  else
                    (let uu____17213 =
                       let uu____17230 = quasi_pattern env lhs  in
                       let uu____17237 = quasi_pattern env rhs  in
                       (uu____17230, uu____17237)  in
                     match uu____17213 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17280 = lhs  in
                         (match uu____17280 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17281;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17283;_},u_lhs,uu____17285)
                              ->
                              let uu____17288 = rhs  in
                              (match uu____17288 with
                               | Flex (uu____17289,u_rhs,uu____17291) ->
                                   let uu____17292 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17292
                                   then
                                     let uu____17299 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17299
                                   else
                                     (let uu____17302 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17302 with
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
                                          let uu____17334 =
                                            let uu____17341 =
                                              let uu____17344 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17344
                                               in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____17341
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17334 with
                                           | (uu____17350,w,wl1) ->
                                               let w_app =
                                                 let uu____17356 =
                                                   let uu____17361 =
                                                     FStar_List.map
                                                       (fun uu____17372  ->
                                                          match uu____17372
                                                          with
                                                          | (z,uu____17380)
                                                              ->
                                                              let uu____17385
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  z
                                                                 in
                                                              FStar_Syntax_Syntax.as_arg
                                                                uu____17385)
                                                       zs
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     w uu____17361
                                                    in
                                                 uu____17356
                                                   FStar_Pervasives_Native.None
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17387 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17387
                                                 then
                                                   let uu____17392 =
                                                     let uu____17396 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17398 =
                                                       let uu____17402 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17404 =
                                                         let uu____17408 =
                                                           term_to_string w
                                                            in
                                                         let uu____17410 =
                                                           let uu____17414 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17423 =
                                                             let uu____17427
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17436
                                                               =
                                                               let uu____17440
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17440]
                                                                in
                                                             uu____17427 ::
                                                               uu____17436
                                                              in
                                                           uu____17414 ::
                                                             uu____17423
                                                            in
                                                         uu____17408 ::
                                                           uu____17410
                                                          in
                                                       uu____17402 ::
                                                         uu____17404
                                                        in
                                                     uu____17396 ::
                                                       uu____17398
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17392
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17457 =
                                                       let uu____17462 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17462)
                                                        in
                                                     TERM uu____17457  in
                                                   let uu____17463 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17463
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17471 =
                                                          let uu____17476 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17476)
                                                           in
                                                        TERM uu____17471  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17477 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17477))))))
                     | uu____17478 ->
                         let uu____17495 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17495)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17549 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17549
            then
              let uu____17554 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17556 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17558 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17560 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17554 uu____17556 uu____17558 uu____17560
            else ());
           (let uu____17571 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17571 with
            | (head1,args1) ->
                let uu____17614 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17614 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17684 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17684 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17689 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17689)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17710 =
                         mklstr
                           (fun uu____17721  ->
                              let uu____17722 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17724 = args_to_string args1  in
                              let uu____17728 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17730 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17722 uu____17724 uu____17728
                                uu____17730)
                          in
                       giveup env1 uu____17710 orig
                     else
                       (let uu____17737 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17742 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17742 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17737
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2590_17746 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2590_17746.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2590_17746.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2590_17746.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2590_17746.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2590_17746.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2590_17746.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2590_17746.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2590_17746.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17756 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17756
                                    else solve env1 wl2))
                        else
                          (let uu____17761 = base_and_refinement env1 t1  in
                           match uu____17761 with
                           | (base1,refinement1) ->
                               let uu____17786 = base_and_refinement env1 t2
                                  in
                               (match uu____17786 with
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
                                           let uu____17951 =
                                             FStar_List.fold_right
                                               (fun uu____17991  ->
                                                  fun uu____17992  ->
                                                    match (uu____17991,
                                                            uu____17992)
                                                    with
                                                    | (((a1,uu____18044),
                                                        (a2,uu____18046)),
                                                       (probs,wl3)) ->
                                                        let uu____18095 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18095
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17951 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18138 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18138
                                                 then
                                                   let uu____18143 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18143
                                                 else ());
                                                (let uu____18149 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18149
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
                                                    (let uu____18176 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18176 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18192 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18192
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18200 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18200))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18225 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18225 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18241 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18241
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18249 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18249)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18277 =
                                           match uu____18277 with
                                           | (prob,reason) ->
                                               ((let uu____18294 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18294
                                                 then
                                                   let uu____18299 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18301 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18299 uu____18301
                                                 else ());
                                                (let uu____18307 =
                                                   let uu____18316 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18319 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18316, uu____18319)
                                                    in
                                                 match uu____18307 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18332 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18332 with
                                                      | (head1',uu____18350)
                                                          ->
                                                          let uu____18375 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18375
                                                           with
                                                           | (head2',uu____18393)
                                                               ->
                                                               let uu____18418
                                                                 =
                                                                 let uu____18423
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18424
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18423,
                                                                   uu____18424)
                                                                  in
                                                               (match uu____18418
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18426
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18426
                                                                    then
                                                                    let uu____18431
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18433
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18435
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18437
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18431
                                                                    uu____18433
                                                                    uu____18435
                                                                    uu____18437
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18442
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2678_18450
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2678_18450.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18452
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18452
                                                                    then
                                                                    let uu____18457
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18457
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18462 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18474 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18474 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18482 =
                                             let uu____18483 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18483.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18482 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18488 -> false  in
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
                                          | uu____18491 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18494 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2698_18530 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2698_18530.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2698_18530.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2698_18530.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2698_18530.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2698_18530.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2698_18530.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2698_18530.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2698_18530.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18606 = destruct_flex_t scrutinee wl1  in
             match uu____18606 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18617 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18617 with
                  | (xs,pat_term,uu____18633,uu____18634) ->
                      let uu____18639 =
                        FStar_List.fold_left
                          (fun uu____18662  ->
                             fun x  ->
                               match uu____18662 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18683 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18683 with
                                    | (uu____18702,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18639 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18723 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18723 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2739_18740 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2739_18740.wl_deferred_to_tac);
                                    ctr = (uu___2739_18740.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2739_18740.umax_heuristic_ok);
                                    tcenv = (uu___2739_18740.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18751 = solve env1 wl'  in
                                (match uu____18751 with
                                 | Success (uu____18754,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2748_18758 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2748_18758.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2748_18758.wl_deferred_to_tac);
                                         ctr = (uu___2748_18758.ctr);
                                         defer_ok =
                                           (uu___2748_18758.defer_ok);
                                         smt_ok = (uu___2748_18758.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2748_18758.umax_heuristic_ok);
                                         tcenv = (uu___2748_18758.tcenv);
                                         wl_implicits =
                                           (uu___2748_18758.wl_implicits)
                                       }  in
                                     let uu____18759 = solve env1 wl'1  in
                                     (match uu____18759 with
                                      | Success
                                          (uu____18762,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18766 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18766))
                                      | Failed uu____18772 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18778 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18801 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18801
                 then
                   let uu____18806 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18808 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18806 uu____18808
                 else ());
                (let uu____18813 =
                   let uu____18834 =
                     let uu____18843 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18843)  in
                   let uu____18850 =
                     let uu____18859 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18859)  in
                   (uu____18834, uu____18850)  in
                 match uu____18813 with
                 | ((uu____18889,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18892;
                                   FStar_Syntax_Syntax.vars = uu____18893;_}),
                    (s,t)) ->
                     let uu____18964 =
                       let uu____18966 = is_flex scrutinee  in
                       Prims.op_Negation uu____18966  in
                     if uu____18964
                     then
                       ((let uu____18977 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18977
                         then
                           let uu____18982 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18982
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19001 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19001
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19016 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19016
                           then
                             let uu____19021 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19023 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19021 uu____19023
                           else ());
                          (let pat_discriminates uu___28_19048 =
                             match uu___28_19048 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19064;
                                  FStar_Syntax_Syntax.p = uu____19065;_},FStar_Pervasives_Native.None
                                ,uu____19066) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19080;
                                  FStar_Syntax_Syntax.p = uu____19081;_},FStar_Pervasives_Native.None
                                ,uu____19082) -> true
                             | uu____19109 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19212 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19212 with
                                       | (uu____19214,uu____19215,t') ->
                                           let uu____19233 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19233 with
                                            | (FullMatch ,uu____19245) ->
                                                true
                                            | (HeadMatch
                                               uu____19259,uu____19260) ->
                                                true
                                            | uu____19275 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19312 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19312
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19323 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19323 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19411,uu____19412) ->
                                       branches1
                                   | uu____19557 -> branches  in
                                 let uu____19612 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19621 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19621 with
                                        | (p,uu____19625,uu____19626) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19655  -> FStar_Util.Inr _19655)
                                   uu____19612))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19685 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19685 with
                                | (p,uu____19694,e) ->
                                    ((let uu____19713 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19713
                                      then
                                        let uu____19718 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19720 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19718 uu____19720
                                      else ());
                                     (let uu____19725 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19740  -> FStar_Util.Inr _19740)
                                        uu____19725)))))
                 | ((s,t),(uu____19743,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19746;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19747;_}))
                     ->
                     let uu____19816 =
                       let uu____19818 = is_flex scrutinee  in
                       Prims.op_Negation uu____19818  in
                     if uu____19816
                     then
                       ((let uu____19829 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19829
                         then
                           let uu____19834 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19834
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19853 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19853
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19868 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19868
                           then
                             let uu____19873 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19875 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19873 uu____19875
                           else ());
                          (let pat_discriminates uu___28_19900 =
                             match uu___28_19900 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19916;
                                  FStar_Syntax_Syntax.p = uu____19917;_},FStar_Pervasives_Native.None
                                ,uu____19918) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19932;
                                  FStar_Syntax_Syntax.p = uu____19933;_},FStar_Pervasives_Native.None
                                ,uu____19934) -> true
                             | uu____19961 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20064 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20064 with
                                       | (uu____20066,uu____20067,t') ->
                                           let uu____20085 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20085 with
                                            | (FullMatch ,uu____20097) ->
                                                true
                                            | (HeadMatch
                                               uu____20111,uu____20112) ->
                                                true
                                            | uu____20127 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20164 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20164
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20175 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20175 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20263,uu____20264) ->
                                       branches1
                                   | uu____20409 -> branches  in
                                 let uu____20464 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20473 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20473 with
                                        | (p,uu____20477,uu____20478) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20507  -> FStar_Util.Inr _20507)
                                   uu____20464))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20537 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20537 with
                                | (p,uu____20546,e) ->
                                    ((let uu____20565 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20565
                                      then
                                        let uu____20570 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20572 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20570 uu____20572
                                      else ());
                                     (let uu____20577 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20592  -> FStar_Util.Inr _20592)
                                        uu____20577)))))
                 | uu____20593 ->
                     ((let uu____20615 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20615
                       then
                         let uu____20620 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20622 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20620 uu____20622
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20668 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20668
            then
              let uu____20673 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20675 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20677 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20679 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20673 uu____20675 uu____20677 uu____20679
            else ());
           (let uu____20684 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20684 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20715,uu____20716) ->
                     let rec may_relate head3 =
                       let uu____20744 =
                         let uu____20745 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20745.FStar_Syntax_Syntax.n  in
                       match uu____20744 with
                       | FStar_Syntax_Syntax.Tm_name uu____20749 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20751 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20776 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20776 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20778 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20781
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20782 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20785,uu____20786) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20828) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20834) ->
                           may_relate t
                       | uu____20839 -> false  in
                     let uu____20841 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20841 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20854 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20854
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20864 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20864
                          then
                            let uu____20867 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20867 with
                             | (guard,wl2) ->
                                 let uu____20874 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20874)
                          else
                            (let uu____20877 =
                               mklstr
                                 (fun uu____20888  ->
                                    let uu____20889 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20891 =
                                      let uu____20893 =
                                        let uu____20897 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20897
                                          (fun x  ->
                                             let uu____20904 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20904)
                                         in
                                      FStar_Util.dflt "" uu____20893  in
                                    let uu____20909 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20911 =
                                      let uu____20913 =
                                        let uu____20917 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20917
                                          (fun x  ->
                                             let uu____20924 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20924)
                                         in
                                      FStar_Util.dflt "" uu____20913  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20889 uu____20891 uu____20909
                                      uu____20911)
                                in
                             giveup env1 uu____20877 orig))
                 | (HeadMatch (true ),uu____20930) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20945 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20945 with
                        | (guard,wl2) ->
                            let uu____20952 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20952)
                     else
                       (let uu____20955 =
                          mklstr
                            (fun uu____20962  ->
                               let uu____20963 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20965 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20963 uu____20965)
                           in
                        giveup env1 uu____20955 orig)
                 | (uu____20968,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2930_20982 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2930_20982.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2930_20982.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2930_20982.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2930_20982.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2930_20982.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2930_20982.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2930_20982.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2930_20982.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____21009 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____21009
          then
            let uu____21012 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____21012
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____21018 =
                let uu____21021 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21021  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21018 t1);
             (let uu____21040 =
                let uu____21043 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21043  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21040 t2);
             (let uu____21062 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21062
              then
                let uu____21066 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21068 =
                  let uu____21070 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21072 =
                    let uu____21074 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21074  in
                  Prims.op_Hat uu____21070 uu____21072  in
                let uu____21077 =
                  let uu____21079 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21081 =
                    let uu____21083 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21083  in
                  Prims.op_Hat uu____21079 uu____21081  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21066 uu____21068 uu____21077
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21090,uu____21091) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21107,FStar_Syntax_Syntax.Tm_delayed uu____21108) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21124,uu____21125) ->
                  let uu____21152 =
                    let uu___2961_21153 = problem  in
                    let uu____21154 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2961_21153.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21154;
                      FStar_TypeChecker_Common.relation =
                        (uu___2961_21153.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2961_21153.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2961_21153.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2961_21153.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2961_21153.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2961_21153.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2961_21153.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2961_21153.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21152 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21155,uu____21156) ->
                  let uu____21163 =
                    let uu___2967_21164 = problem  in
                    let uu____21165 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2967_21164.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21165;
                      FStar_TypeChecker_Common.relation =
                        (uu___2967_21164.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2967_21164.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2967_21164.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2967_21164.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2967_21164.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2967_21164.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2967_21164.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2967_21164.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21163 wl
              | (uu____21166,FStar_Syntax_Syntax.Tm_ascribed uu____21167) ->
                  let uu____21194 =
                    let uu___2973_21195 = problem  in
                    let uu____21196 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2973_21195.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2973_21195.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2973_21195.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21196;
                      FStar_TypeChecker_Common.element =
                        (uu___2973_21195.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2973_21195.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2973_21195.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2973_21195.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2973_21195.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2973_21195.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21194 wl
              | (uu____21197,FStar_Syntax_Syntax.Tm_meta uu____21198) ->
                  let uu____21205 =
                    let uu___2979_21206 = problem  in
                    let uu____21207 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2979_21206.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2979_21206.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2979_21206.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21207;
                      FStar_TypeChecker_Common.element =
                        (uu___2979_21206.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2979_21206.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2979_21206.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2979_21206.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2979_21206.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2979_21206.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21205 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21209),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21211)) ->
                  let uu____21220 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21220
              | (FStar_Syntax_Syntax.Tm_bvar uu____21221,uu____21222) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21224,FStar_Syntax_Syntax.Tm_bvar uu____21225) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_21295 =
                    match uu___29_21295 with
                    | [] -> c
                    | bs ->
                        let uu____21323 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21323
                     in
                  let uu____21334 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21334 with
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
                                    let uu____21483 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21483
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
                  let mk_t t l uu___30_21572 =
                    match uu___30_21572 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21614 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21614 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21759 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21760 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21759
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21760 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21762,uu____21763) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21794 -> true
                    | uu____21814 -> false  in
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
                      (let uu____21874 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3081_21882 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3081_21882.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3081_21882.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3081_21882.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3081_21882.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3081_21882.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3081_21882.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3081_21882.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3081_21882.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3081_21882.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3081_21882.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3081_21882.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3081_21882.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3081_21882.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3081_21882.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3081_21882.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3081_21882.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3081_21882.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3081_21882.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3081_21882.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3081_21882.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3081_21882.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3081_21882.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3081_21882.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3081_21882.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3081_21882.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3081_21882.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3081_21882.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3081_21882.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3081_21882.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3081_21882.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3081_21882.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3081_21882.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3081_21882.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3081_21882.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3081_21882.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3081_21882.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3081_21882.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3081_21882.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3081_21882.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3081_21882.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3081_21882.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3081_21882.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3081_21882.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3081_21882.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3081_21882.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21874 with
                       | (uu____21887,ty,uu____21889) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21898 =
                                 let uu____21899 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21899.FStar_Syntax_Syntax.n  in
                               match uu____21898 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21902 ->
                                   let uu____21909 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21909
                               | uu____21910 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21913 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21913
                             then
                               let uu____21918 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21920 =
                                 let uu____21922 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21922
                                  in
                               let uu____21923 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21918 uu____21920 uu____21923
                             else ());
                            r1))
                     in
                  let uu____21928 =
                    let uu____21945 = maybe_eta t1  in
                    let uu____21952 = maybe_eta t2  in
                    (uu____21945, uu____21952)  in
                  (match uu____21928 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3102_21994 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3102_21994.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3102_21994.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3102_21994.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3102_21994.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3102_21994.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3102_21994.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3102_21994.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3102_21994.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22015 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22015
                       then
                         let uu____22018 = destruct_flex_t not_abs wl  in
                         (match uu____22018 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3119_22035 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3119_22035.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3119_22035.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3119_22035.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3119_22035.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3119_22035.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3119_22035.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3119_22035.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3119_22035.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22038 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22038 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22061 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22061
                       then
                         let uu____22064 = destruct_flex_t not_abs wl  in
                         (match uu____22064 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3119_22081 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3119_22081.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3119_22081.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3119_22081.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3119_22081.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3119_22081.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3119_22081.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3119_22081.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3119_22081.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22084 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22084 orig))
                   | uu____22087 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22105,FStar_Syntax_Syntax.Tm_abs uu____22106) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22137 -> true
                    | uu____22157 -> false  in
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
                      (let uu____22217 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3081_22225 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3081_22225.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3081_22225.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3081_22225.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3081_22225.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3081_22225.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3081_22225.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3081_22225.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3081_22225.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3081_22225.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3081_22225.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3081_22225.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3081_22225.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3081_22225.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3081_22225.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3081_22225.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3081_22225.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3081_22225.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3081_22225.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3081_22225.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3081_22225.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3081_22225.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3081_22225.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3081_22225.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3081_22225.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3081_22225.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3081_22225.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3081_22225.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3081_22225.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3081_22225.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3081_22225.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3081_22225.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3081_22225.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3081_22225.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3081_22225.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3081_22225.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3081_22225.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3081_22225.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3081_22225.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3081_22225.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3081_22225.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3081_22225.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3081_22225.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3081_22225.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3081_22225.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3081_22225.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22217 with
                       | (uu____22230,ty,uu____22232) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22241 =
                                 let uu____22242 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22242.FStar_Syntax_Syntax.n  in
                               match uu____22241 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22245 ->
                                   let uu____22252 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22252
                               | uu____22253 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22256 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22256
                             then
                               let uu____22261 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22263 =
                                 let uu____22265 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22265
                                  in
                               let uu____22266 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22261 uu____22263 uu____22266
                             else ());
                            r1))
                     in
                  let uu____22271 =
                    let uu____22288 = maybe_eta t1  in
                    let uu____22295 = maybe_eta t2  in
                    (uu____22288, uu____22295)  in
                  (match uu____22271 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3102_22337 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3102_22337.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3102_22337.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3102_22337.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3102_22337.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3102_22337.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3102_22337.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3102_22337.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3102_22337.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22358 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22358
                       then
                         let uu____22361 = destruct_flex_t not_abs wl  in
                         (match uu____22361 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3119_22378 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3119_22378.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3119_22378.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3119_22378.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3119_22378.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3119_22378.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3119_22378.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3119_22378.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3119_22378.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22381 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22381 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22404 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22404
                       then
                         let uu____22407 = destruct_flex_t not_abs wl  in
                         (match uu____22407 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3119_22424 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3119_22424.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3119_22424.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3119_22424.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3119_22424.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3119_22424.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3119_22424.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3119_22424.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3119_22424.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22427 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22427 orig))
                   | uu____22430 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22460 =
                    let uu____22465 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22465 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3142_22493 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3142_22493.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3142_22493.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3144_22495 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3144_22495.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3144_22495.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22496,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3142_22511 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3142_22511.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3142_22511.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3144_22513 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3144_22513.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3144_22513.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22514 -> (x1, x2)  in
                  (match uu____22460 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22533 = as_refinement false env t11  in
                       (match uu____22533 with
                        | (x12,phi11) ->
                            let uu____22541 = as_refinement false env t21  in
                            (match uu____22541 with
                             | (x22,phi21) ->
                                 ((let uu____22550 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22550
                                   then
                                     ((let uu____22555 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22557 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22559 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22555
                                         uu____22557 uu____22559);
                                      (let uu____22562 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22564 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22566 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22562
                                         uu____22564 uu____22566))
                                   else ());
                                  (let uu____22571 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22571 with
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
                                         let uu____22642 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22642
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22654 =
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
                                         (let uu____22667 =
                                            let uu____22670 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22670
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22667
                                            (p_guard base_prob));
                                         (let uu____22689 =
                                            let uu____22692 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22692
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22689
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22711 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22711)
                                          in
                                       let has_uvars =
                                         (let uu____22716 =
                                            let uu____22718 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22718
                                             in
                                          Prims.op_Negation uu____22716) ||
                                           (let uu____22722 =
                                              let uu____22724 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22724
                                               in
                                            Prims.op_Negation uu____22722)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22728 =
                                           let uu____22733 =
                                             let uu____22742 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22742]  in
                                           mk_t_problem wl1 uu____22733 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22728 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22765 =
                                                solve env1
                                                  (let uu___3187_22767 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3187_22767.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3187_22767.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3187_22767.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3187_22767.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3187_22767.tcenv);
                                                     wl_implicits =
                                                       (uu___3187_22767.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22765 with
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
                                               | Success
                                                   (uu____22782,defer_to_tac,uu____22784)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22789 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22789
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3203_22798 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3203_22798.attempting);
                                                         wl_deferred =
                                                           (uu___3203_22798.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3203_22798.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3203_22798.defer_ok);
                                                         smt_ok =
                                                           (uu___3203_22798.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3203_22798.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3203_22798.tcenv);
                                                         wl_implicits =
                                                           (uu___3203_22798.wl_implicits)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22801 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22801))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22804,FStar_Syntax_Syntax.Tm_uvar uu____22805) ->
                  let uu____22830 = destruct_flex_t t1 wl  in
                  (match uu____22830 with
                   | (f1,wl1) ->
                       let uu____22837 = destruct_flex_t t2 wl1  in
                       (match uu____22837 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22844;
                    FStar_Syntax_Syntax.pos = uu____22845;
                    FStar_Syntax_Syntax.vars = uu____22846;_},uu____22847),FStar_Syntax_Syntax.Tm_uvar
                 uu____22848) ->
                  let uu____22897 = destruct_flex_t t1 wl  in
                  (match uu____22897 with
                   | (f1,wl1) ->
                       let uu____22904 = destruct_flex_t t2 wl1  in
                       (match uu____22904 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22911,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22912;
                    FStar_Syntax_Syntax.pos = uu____22913;
                    FStar_Syntax_Syntax.vars = uu____22914;_},uu____22915))
                  ->
                  let uu____22964 = destruct_flex_t t1 wl  in
                  (match uu____22964 with
                   | (f1,wl1) ->
                       let uu____22971 = destruct_flex_t t2 wl1  in
                       (match uu____22971 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22978;
                    FStar_Syntax_Syntax.pos = uu____22979;
                    FStar_Syntax_Syntax.vars = uu____22980;_},uu____22981),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22982;
                    FStar_Syntax_Syntax.pos = uu____22983;
                    FStar_Syntax_Syntax.vars = uu____22984;_},uu____22985))
                  ->
                  let uu____23058 = destruct_flex_t t1 wl  in
                  (match uu____23058 with
                   | (f1,wl1) ->
                       let uu____23065 = destruct_flex_t t2 wl1  in
                       (match uu____23065 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23072,uu____23073) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23086 = destruct_flex_t t1 wl  in
                  (match uu____23086 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23093;
                    FStar_Syntax_Syntax.pos = uu____23094;
                    FStar_Syntax_Syntax.vars = uu____23095;_},uu____23096),uu____23097)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23134 = destruct_flex_t t1 wl  in
                  (match uu____23134 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23141,FStar_Syntax_Syntax.Tm_uvar uu____23142) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23155,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23156;
                    FStar_Syntax_Syntax.pos = uu____23157;
                    FStar_Syntax_Syntax.vars = uu____23158;_},uu____23159))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23196,FStar_Syntax_Syntax.Tm_arrow uu____23197) ->
                  solve_t' env
                    (let uu___3304_23225 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3304_23225.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3304_23225.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3304_23225.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3304_23225.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3304_23225.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3304_23225.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3304_23225.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3304_23225.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3304_23225.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23226;
                    FStar_Syntax_Syntax.pos = uu____23227;
                    FStar_Syntax_Syntax.vars = uu____23228;_},uu____23229),FStar_Syntax_Syntax.Tm_arrow
                 uu____23230) ->
                  solve_t' env
                    (let uu___3304_23282 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3304_23282.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3304_23282.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3304_23282.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3304_23282.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3304_23282.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3304_23282.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3304_23282.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3304_23282.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3304_23282.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23283,FStar_Syntax_Syntax.Tm_uvar uu____23284) ->
                  let uu____23297 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23297
              | (uu____23298,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23299;
                    FStar_Syntax_Syntax.pos = uu____23300;
                    FStar_Syntax_Syntax.vars = uu____23301;_},uu____23302))
                  ->
                  let uu____23339 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23339
              | (FStar_Syntax_Syntax.Tm_uvar uu____23340,uu____23341) ->
                  let uu____23354 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23354
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23355;
                    FStar_Syntax_Syntax.pos = uu____23356;
                    FStar_Syntax_Syntax.vars = uu____23357;_},uu____23358),uu____23359)
                  ->
                  let uu____23396 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23396
              | (FStar_Syntax_Syntax.Tm_refine uu____23397,uu____23398) ->
                  let t21 =
                    let uu____23406 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23406  in
                  solve_t env
                    (let uu___3339_23432 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3339_23432.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3339_23432.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3339_23432.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3339_23432.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3339_23432.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3339_23432.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3339_23432.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3339_23432.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3339_23432.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23433,FStar_Syntax_Syntax.Tm_refine uu____23434) ->
                  let t11 =
                    let uu____23442 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23442  in
                  solve_t env
                    (let uu___3346_23468 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3346_23468.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3346_23468.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3346_23468.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3346_23468.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3346_23468.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3346_23468.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3346_23468.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3346_23468.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3346_23468.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23550 =
                    let uu____23551 = guard_of_prob env wl problem t1 t2  in
                    match uu____23551 with
                    | (guard,wl1) ->
                        let uu____23558 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23558
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23777 = br1  in
                        (match uu____23777 with
                         | (p1,w1,uu____23806) ->
                             let uu____23823 = br2  in
                             (match uu____23823 with
                              | (p2,w2,uu____23846) ->
                                  let uu____23851 =
                                    let uu____23853 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23853  in
                                  if uu____23851
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23880 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23880 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23917 = br2  in
                                         (match uu____23917 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23950 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23950
                                                 in
                                              let uu____23955 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23986,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____24007) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24066 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24066 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23955
                                                (fun uu____24138  ->
                                                   match uu____24138 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24175 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24175
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24196
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24196
                                                              then
                                                                let uu____24201
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24203
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24201
                                                                  uu____24203
                                                              else ());
                                                             (let uu____24209
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24209
                                                                (fun
                                                                   uu____24245
                                                                    ->
                                                                   match uu____24245
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
                    | uu____24374 -> FStar_Pervasives_Native.None  in
                  let uu____24415 = solve_branches wl brs1 brs2  in
                  (match uu____24415 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24441 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24441 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24468 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24468 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24502 =
                                FStar_List.map
                                  (fun uu____24514  ->
                                     match uu____24514 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24502  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24523 =
                              let uu____24524 =
                                let uu____24525 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24525
                                  (let uu___3445_24533 = wl3  in
                                   {
                                     attempting =
                                       (uu___3445_24533.attempting);
                                     wl_deferred =
                                       (uu___3445_24533.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3445_24533.wl_deferred_to_tac);
                                     ctr = (uu___3445_24533.ctr);
                                     defer_ok = (uu___3445_24533.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3445_24533.umax_heuristic_ok);
                                     tcenv = (uu___3445_24533.tcenv);
                                     wl_implicits =
                                       (uu___3445_24533.wl_implicits)
                                   })
                                 in
                              solve env uu____24524  in
                            (match uu____24523 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24539 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24548 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24548 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24551,uu____24552) ->
                  let head1 =
                    let uu____24576 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24576
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24622 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24622
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24668 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24668
                    then
                      let uu____24672 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24674 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24676 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24672 uu____24674 uu____24676
                    else ());
                   (let no_free_uvars t =
                      (let uu____24690 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24690) &&
                        (let uu____24694 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24694)
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
                      let uu____24713 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24713 = FStar_Syntax_Util.Equal  in
                    let uu____24714 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24714
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24718 = equal t1 t2  in
                         (if uu____24718
                          then
                            let uu____24721 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24721
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24726 =
                            let uu____24733 = equal t1 t2  in
                            if uu____24733
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24746 = mk_eq2 wl env orig t1 t2  in
                               match uu____24746 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24726 with
                          | (guard,wl1) ->
                              let uu____24767 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24767))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24770,uu____24771) ->
                  let head1 =
                    let uu____24779 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24779
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24825 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24825
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24871 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24871
                    then
                      let uu____24875 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24877 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24879 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24875 uu____24877 uu____24879
                    else ());
                   (let no_free_uvars t =
                      (let uu____24893 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24893) &&
                        (let uu____24897 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24897)
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
                      let uu____24916 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24916 = FStar_Syntax_Util.Equal  in
                    let uu____24917 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24917
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24921 = equal t1 t2  in
                         (if uu____24921
                          then
                            let uu____24924 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24924
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24929 =
                            let uu____24936 = equal t1 t2  in
                            if uu____24936
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24949 = mk_eq2 wl env orig t1 t2  in
                               match uu____24949 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24929 with
                          | (guard,wl1) ->
                              let uu____24970 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24970))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24973,uu____24974) ->
                  let head1 =
                    let uu____24976 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24976
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25022 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25022
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25068 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25068
                    then
                      let uu____25072 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25074 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25076 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25072 uu____25074 uu____25076
                    else ());
                   (let no_free_uvars t =
                      (let uu____25090 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25090) &&
                        (let uu____25094 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25094)
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
                      let uu____25113 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25113 = FStar_Syntax_Util.Equal  in
                    let uu____25114 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25114
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25118 = equal t1 t2  in
                         (if uu____25118
                          then
                            let uu____25121 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25121
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25126 =
                            let uu____25133 = equal t1 t2  in
                            if uu____25133
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25146 = mk_eq2 wl env orig t1 t2  in
                               match uu____25146 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25126 with
                          | (guard,wl1) ->
                              let uu____25167 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25167))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25170,uu____25171) ->
                  let head1 =
                    let uu____25173 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25173
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25219 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25219
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25265 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25265
                    then
                      let uu____25269 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25271 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25273 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25269 uu____25271 uu____25273
                    else ());
                   (let no_free_uvars t =
                      (let uu____25287 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25287) &&
                        (let uu____25291 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25291)
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
                      let uu____25310 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25310 = FStar_Syntax_Util.Equal  in
                    let uu____25311 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25311
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25315 = equal t1 t2  in
                         (if uu____25315
                          then
                            let uu____25318 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25318
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25323 =
                            let uu____25330 = equal t1 t2  in
                            if uu____25330
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25343 = mk_eq2 wl env orig t1 t2  in
                               match uu____25343 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25323 with
                          | (guard,wl1) ->
                              let uu____25364 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25364))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25367,uu____25368) ->
                  let head1 =
                    let uu____25370 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25370
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25410 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25410
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25450 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25450
                    then
                      let uu____25454 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25456 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25458 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25454 uu____25456 uu____25458
                    else ());
                   (let no_free_uvars t =
                      (let uu____25472 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25472) &&
                        (let uu____25476 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25476)
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
                      let uu____25495 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25495 = FStar_Syntax_Util.Equal  in
                    let uu____25496 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25496
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25500 = equal t1 t2  in
                         (if uu____25500
                          then
                            let uu____25503 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25503
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25508 =
                            let uu____25515 = equal t1 t2  in
                            if uu____25515
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25528 = mk_eq2 wl env orig t1 t2  in
                               match uu____25528 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25508 with
                          | (guard,wl1) ->
                              let uu____25549 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25549))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25552,uu____25553) ->
                  let head1 =
                    let uu____25571 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25571
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25611 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25611
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25651 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25651
                    then
                      let uu____25655 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25657 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25659 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25655 uu____25657 uu____25659
                    else ());
                   (let no_free_uvars t =
                      (let uu____25673 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25673) &&
                        (let uu____25677 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25677)
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
                      let uu____25696 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25696 = FStar_Syntax_Util.Equal  in
                    let uu____25697 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25697
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25701 = equal t1 t2  in
                         (if uu____25701
                          then
                            let uu____25704 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25704
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25709 =
                            let uu____25716 = equal t1 t2  in
                            if uu____25716
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25729 = mk_eq2 wl env orig t1 t2  in
                               match uu____25729 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25709 with
                          | (guard,wl1) ->
                              let uu____25750 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25750))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25753,FStar_Syntax_Syntax.Tm_match uu____25754) ->
                  let head1 =
                    let uu____25778 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25778
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25818 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25818
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25858 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25858
                    then
                      let uu____25862 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25864 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25866 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25862 uu____25864 uu____25866
                    else ());
                   (let no_free_uvars t =
                      (let uu____25880 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25880) &&
                        (let uu____25884 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25884)
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
                      let uu____25903 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25903 = FStar_Syntax_Util.Equal  in
                    let uu____25904 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25904
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25908 = equal t1 t2  in
                         (if uu____25908
                          then
                            let uu____25911 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25911
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25916 =
                            let uu____25923 = equal t1 t2  in
                            if uu____25923
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25936 = mk_eq2 wl env orig t1 t2  in
                               match uu____25936 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25916 with
                          | (guard,wl1) ->
                              let uu____25957 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25957))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25960,FStar_Syntax_Syntax.Tm_uinst uu____25961) ->
                  let head1 =
                    let uu____25969 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25969
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26009 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26009
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26049 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26049
                    then
                      let uu____26053 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26055 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26057 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26053 uu____26055 uu____26057
                    else ());
                   (let no_free_uvars t =
                      (let uu____26071 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26071) &&
                        (let uu____26075 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26075)
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
                      let uu____26094 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26094 = FStar_Syntax_Util.Equal  in
                    let uu____26095 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26095
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26099 = equal t1 t2  in
                         (if uu____26099
                          then
                            let uu____26102 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26102
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26107 =
                            let uu____26114 = equal t1 t2  in
                            if uu____26114
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26127 = mk_eq2 wl env orig t1 t2  in
                               match uu____26127 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26107 with
                          | (guard,wl1) ->
                              let uu____26148 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26148))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26151,FStar_Syntax_Syntax.Tm_name uu____26152) ->
                  let head1 =
                    let uu____26154 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26154
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26194 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26194
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26234 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26234
                    then
                      let uu____26238 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26240 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26242 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26238 uu____26240 uu____26242
                    else ());
                   (let no_free_uvars t =
                      (let uu____26256 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26256) &&
                        (let uu____26260 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26260)
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
                      let uu____26279 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26279 = FStar_Syntax_Util.Equal  in
                    let uu____26280 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26280
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26284 = equal t1 t2  in
                         (if uu____26284
                          then
                            let uu____26287 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26287
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26292 =
                            let uu____26299 = equal t1 t2  in
                            if uu____26299
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26312 = mk_eq2 wl env orig t1 t2  in
                               match uu____26312 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26292 with
                          | (guard,wl1) ->
                              let uu____26333 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26333))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26336,FStar_Syntax_Syntax.Tm_constant uu____26337) ->
                  let head1 =
                    let uu____26339 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26339
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26379 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26379
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26419 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26419
                    then
                      let uu____26423 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26425 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26427 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26423 uu____26425 uu____26427
                    else ());
                   (let no_free_uvars t =
                      (let uu____26441 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26441) &&
                        (let uu____26445 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26445)
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
                      let uu____26464 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26464 = FStar_Syntax_Util.Equal  in
                    let uu____26465 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26465
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26469 = equal t1 t2  in
                         (if uu____26469
                          then
                            let uu____26472 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26472
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26477 =
                            let uu____26484 = equal t1 t2  in
                            if uu____26484
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26497 = mk_eq2 wl env orig t1 t2  in
                               match uu____26497 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26477 with
                          | (guard,wl1) ->
                              let uu____26518 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26518))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26521,FStar_Syntax_Syntax.Tm_fvar uu____26522) ->
                  let head1 =
                    let uu____26524 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26524
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26570 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26570
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26616 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26616
                    then
                      let uu____26620 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26622 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26624 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26620 uu____26622 uu____26624
                    else ());
                   (let no_free_uvars t =
                      (let uu____26638 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26638) &&
                        (let uu____26642 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26642)
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
                      let uu____26661 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26661 = FStar_Syntax_Util.Equal  in
                    let uu____26662 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26662
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26666 = equal t1 t2  in
                         (if uu____26666
                          then
                            let uu____26669 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26669
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26674 =
                            let uu____26681 = equal t1 t2  in
                            if uu____26681
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26694 = mk_eq2 wl env orig t1 t2  in
                               match uu____26694 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26674 with
                          | (guard,wl1) ->
                              let uu____26715 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26715))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26718,FStar_Syntax_Syntax.Tm_app uu____26719) ->
                  let head1 =
                    let uu____26737 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26737
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26777 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26777
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26817 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26817
                    then
                      let uu____26821 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26823 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26825 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26821 uu____26823 uu____26825
                    else ());
                   (let no_free_uvars t =
                      (let uu____26839 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26839) &&
                        (let uu____26843 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26843)
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
                      let uu____26862 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26862 = FStar_Syntax_Util.Equal  in
                    let uu____26863 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26863
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26867 = equal t1 t2  in
                         (if uu____26867
                          then
                            let uu____26870 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26870
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26875 =
                            let uu____26882 = equal t1 t2  in
                            if uu____26882
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26895 = mk_eq2 wl env orig t1 t2  in
                               match uu____26895 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26875 with
                          | (guard,wl1) ->
                              let uu____26916 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26916))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26919,FStar_Syntax_Syntax.Tm_let uu____26920) ->
                  let uu____26947 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26947
                  then
                    let uu____26950 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26950
                  else
                    (let uu____26953 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26953 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26956,uu____26957) ->
                  let uu____26971 =
                    let uu____26977 =
                      let uu____26979 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26981 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26983 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26985 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26979 uu____26981 uu____26983 uu____26985
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26977)
                     in
                  FStar_Errors.raise_error uu____26971
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26989,FStar_Syntax_Syntax.Tm_let uu____26990) ->
                  let uu____27004 =
                    let uu____27010 =
                      let uu____27012 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27014 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27016 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27018 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27012 uu____27014 uu____27016 uu____27018
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27010)
                     in
                  FStar_Errors.raise_error uu____27004
                    t1.FStar_Syntax_Syntax.pos
              | uu____27022 ->
                  let uu____27027 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____27027 orig))))

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
          (let uu____27093 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27093
           then
             let uu____27098 =
               let uu____27100 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27100  in
             let uu____27101 =
               let uu____27103 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27103  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27098 uu____27101
           else ());
          (let uu____27107 =
             let uu____27109 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27109  in
           if uu____27107
           then
             let uu____27112 =
               mklstr
                 (fun uu____27119  ->
                    let uu____27120 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27122 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27120 uu____27122)
                in
             giveup env uu____27112 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27144 =
                  mklstr
                    (fun uu____27151  ->
                       let uu____27152 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27154 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27152 uu____27154)
                   in
                giveup env uu____27144 orig)
             else
               (let uu____27159 =
                  FStar_List.fold_left2
                    (fun uu____27180  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27180 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27201 =
                                 let uu____27206 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27207 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27206
                                   FStar_TypeChecker_Common.EQ uu____27207
                                   "effect universes"
                                  in
                               (match uu____27201 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27159 with
                | (univ_sub_probs,wl1) ->
                    let uu____27227 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27227 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27235 =
                           FStar_List.fold_right2
                             (fun uu____27272  ->
                                fun uu____27273  ->
                                  fun uu____27274  ->
                                    match (uu____27272, uu____27273,
                                            uu____27274)
                                    with
                                    | ((a1,uu____27318),(a2,uu____27320),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27353 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27353 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27235 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27380 =
                                  let uu____27383 =
                                    let uu____27386 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27386
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27383
                                   in
                                FStar_List.append univ_sub_probs uu____27380
                                 in
                              let guard =
                                let guard =
                                  let uu____27408 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27408  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3598_27417 = wl3  in
                                {
                                  attempting = (uu___3598_27417.attempting);
                                  wl_deferred = (uu___3598_27417.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3598_27417.wl_deferred_to_tac);
                                  ctr = (uu___3598_27417.ctr);
                                  defer_ok = (uu___3598_27417.defer_ok);
                                  smt_ok = (uu___3598_27417.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3598_27417.umax_heuristic_ok);
                                  tcenv = (uu___3598_27417.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27419 = attempt sub_probs wl5  in
                              solve env uu____27419))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27437 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27437
           then
             let uu____27442 =
               let uu____27444 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27444
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27446 =
               let uu____27448 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27448
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27442 uu____27446
           else ());
          (let uu____27453 =
             let uu____27458 =
               let uu____27463 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27463
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27458
               (fun uu____27480  ->
                  match uu____27480 with
                  | (c,g) ->
                      let uu____27491 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27491, g))
              in
           match uu____27453 with
           | (c12,g_lift) ->
               ((let uu____27495 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27495
                 then
                   let uu____27500 =
                     let uu____27502 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27502
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27504 =
                     let uu____27506 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27506
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27500 uu____27504
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3618_27516 = wl  in
                     {
                       attempting = (uu___3618_27516.attempting);
                       wl_deferred = (uu___3618_27516.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3618_27516.wl_deferred_to_tac);
                       ctr = (uu___3618_27516.ctr);
                       defer_ok = (uu___3618_27516.defer_ok);
                       smt_ok = (uu___3618_27516.smt_ok);
                       umax_heuristic_ok =
                         (uu___3618_27516.umax_heuristic_ok);
                       tcenv = (uu___3618_27516.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____27517 =
                     let rec is_uvar1 t =
                       let uu____27531 =
                         let uu____27532 = FStar_Syntax_Subst.compress t  in
                         uu____27532.FStar_Syntax_Syntax.n  in
                       match uu____27531 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27536 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27551) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27557) ->
                           is_uvar1 t1
                       | uu____27582 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27616  ->
                          fun uu____27617  ->
                            fun uu____27618  ->
                              match (uu____27616, uu____27617, uu____27618)
                              with
                              | ((a1,uu____27662),(a2,uu____27664),(is_sub_probs,wl2))
                                  ->
                                  let uu____27697 = is_uvar1 a1  in
                                  if uu____27697
                                  then
                                    ((let uu____27707 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27707
                                      then
                                        let uu____27712 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27714 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27712 uu____27714
                                      else ());
                                     (let uu____27719 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27719 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27517 with
                   | (is_sub_probs,wl2) ->
                       let uu____27747 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27747 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27755 =
                              let uu____27760 =
                                let uu____27761 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27761
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27760
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27755 with
                             | (uu____27768,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27779 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27781 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27779 s uu____27781
                                    in
                                 let uu____27784 =
                                   let uu____27813 =
                                     let uu____27814 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27814.FStar_Syntax_Syntax.n  in
                                   match uu____27813 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27874 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27874 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27937 =
                                              let uu____27956 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27956
                                                (fun uu____28060  ->
                                                   match uu____28060 with
                                                   | (l1,l2) ->
                                                       let uu____28133 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28133))
                                               in
                                            (match uu____27937 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28238 ->
                                       let uu____28239 =
                                         let uu____28245 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28245)
                                          in
                                       FStar_Errors.raise_error uu____28239 r
                                    in
                                 (match uu____27784 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28321 =
                                        let uu____28328 =
                                          let uu____28329 =
                                            let uu____28330 =
                                              let uu____28337 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28337,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28330
                                             in
                                          [uu____28329]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28328
                                          (fun b  ->
                                             let uu____28353 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28355 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28357 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28353 uu____28355
                                               uu____28357) r
                                         in
                                      (match uu____28321 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28367 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28367
                                             then
                                               let uu____28372 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28381 =
                                                          let uu____28383 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28383
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28381) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28372
                                             else ());
                                            (let wl4 =
                                               let uu___3690_28391 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3690_28391.attempting);
                                                 wl_deferred =
                                                   (uu___3690_28391.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3690_28391.wl_deferred_to_tac);
                                                 ctr = (uu___3690_28391.ctr);
                                                 defer_ok =
                                                   (uu___3690_28391.defer_ok);
                                                 smt_ok =
                                                   (uu___3690_28391.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3690_28391.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3690_28391.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28416 =
                                                        let uu____28423 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28423, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28416) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28440 =
                                               let f_sort_is =
                                                 let uu____28450 =
                                                   let uu____28451 =
                                                     let uu____28454 =
                                                       let uu____28455 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28455.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28454
                                                      in
                                                   uu____28451.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28450 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28466,uu____28467::is)
                                                     ->
                                                     let uu____28509 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28509
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28542 ->
                                                     let uu____28543 =
                                                       let uu____28549 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28549)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28543 r
                                                  in
                                               let uu____28555 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28590  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28590
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28611 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28611
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28555
                                                in
                                             match uu____28440 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28636 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28636
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28637 =
                                                   let g_sort_is =
                                                     let uu____28647 =
                                                       let uu____28648 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28648.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28647 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28653,uu____28654::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28714 ->
                                                         let uu____28715 =
                                                           let uu____28721 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28721)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28715 r
                                                      in
                                                   let uu____28727 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28762  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28762
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28783
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28783
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28727
                                                    in
                                                 (match uu____28637 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28810 =
                                                          let uu____28815 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28816 =
                                                            let uu____28817 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28817
                                                             in
                                                          (uu____28815,
                                                            uu____28816)
                                                           in
                                                        match uu____28810
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28845 =
                                                          let uu____28848 =
                                                            let uu____28851 =
                                                              let uu____28854
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28854
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28851
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28848
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28845
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28878 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28878
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
                                                        let uu____28889 =
                                                          let uu____28892 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28895  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28895)
                                                            uu____28892
                                                           in
                                                        solve_prob orig
                                                          uu____28889 [] wl6
                                                         in
                                                      let uu____28896 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28896))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28919 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28921 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28921]
              | x -> x  in
            let c12 =
              let uu___3756_28924 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3756_28924.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3756_28924.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3756_28924.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3756_28924.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28925 =
              let uu____28930 =
                FStar_All.pipe_right
                  (let uu___3759_28932 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3759_28932.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3759_28932.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3759_28932.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3759_28932.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28930
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28925
              (fun uu____28946  ->
                 match uu____28946 with
                 | (c,g) ->
                     let uu____28953 =
                       let uu____28955 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28955  in
                     if uu____28953
                     then
                       let uu____28958 =
                         let uu____28964 =
                           let uu____28966 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28968 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28966 uu____28968
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28964)
                          in
                       FStar_Errors.raise_error uu____28958 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28974 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28974
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28980 = lift_c1 ()  in
               solve_eq uu____28980 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28989  ->
                         match uu___31_28989 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28994 -> false))
                  in
               let uu____28996 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____29026)::uu____29027,(wp2,uu____29029)::uu____29030)
                     -> (wp1, wp2)
                 | uu____29103 ->
                     let uu____29128 =
                       let uu____29134 =
                         let uu____29136 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____29138 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____29136 uu____29138
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____29134)
                        in
                     FStar_Errors.raise_error uu____29128
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28996 with
               | (wpc1,wpc2) ->
                   let uu____29148 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____29148
                   then
                     let uu____29151 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29151 wl
                   else
                     (let uu____29155 =
                        let uu____29162 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____29162  in
                      match uu____29155 with
                      | (c2_decl,qualifiers) ->
                          let uu____29183 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____29183
                          then
                            let c1_repr =
                              let uu____29190 =
                                let uu____29191 =
                                  let uu____29192 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____29192  in
                                let uu____29193 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29191 uu____29193
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29190
                               in
                            let c2_repr =
                              let uu____29196 =
                                let uu____29197 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____29198 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29197 uu____29198
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29196
                               in
                            let uu____29200 =
                              let uu____29205 =
                                let uu____29207 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____29209 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____29207
                                  uu____29209
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____29205
                               in
                            (match uu____29200 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____29215 = attempt [prob] wl2  in
                                 solve env uu____29215)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____29235 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____29235
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____29258 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____29258
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
                                        let uu____29268 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____29268 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____29275 =
                                        let uu____29282 =
                                          let uu____29283 =
                                            let uu____29300 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29303 =
                                              let uu____29314 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29314; wpc1_2]  in
                                            (uu____29300, uu____29303)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29283
                                           in
                                        FStar_Syntax_Syntax.mk uu____29282
                                         in
                                      uu____29275
                                        FStar_Pervasives_Native.None r))
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
                                     let uu____29363 =
                                       let uu____29370 =
                                         let uu____29371 =
                                           let uu____29388 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29391 =
                                             let uu____29402 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29411 =
                                               let uu____29422 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29422; wpc1_2]  in
                                             uu____29402 :: uu____29411  in
                                           (uu____29388, uu____29391)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29371
                                          in
                                       FStar_Syntax_Syntax.mk uu____29370  in
                                     uu____29363 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____29476 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____29476
                              then
                                let uu____29481 =
                                  let uu____29483 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____29483
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____29481
                              else ());
                             (let uu____29487 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____29487 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____29496 =
                                      let uu____29499 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _29502  ->
                                           FStar_Pervasives_Native.Some
                                             _29502) uu____29499
                                       in
                                    solve_prob orig uu____29496 [] wl1  in
                                  let uu____29503 = attempt [base_prob] wl2
                                     in
                                  solve env uu____29503))))
           in
        let uu____29504 = FStar_Util.physical_equality c1 c2  in
        if uu____29504
        then
          let uu____29507 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29507
        else
          ((let uu____29511 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29511
            then
              let uu____29516 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29518 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29516
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29518
            else ());
           (let uu____29523 =
              let uu____29532 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29535 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29532, uu____29535)  in
            match uu____29523 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29553),FStar_Syntax_Syntax.Total
                    (t2,uu____29555)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29572 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29572 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29574,FStar_Syntax_Syntax.Total uu____29575) ->
                     let uu____29592 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29592 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29596),FStar_Syntax_Syntax.Total
                    (t2,uu____29598)) ->
                     let uu____29615 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29615 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29618),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29620)) ->
                     let uu____29637 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29637 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29640),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29642)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29659 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29659 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29662),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29664)) ->
                     let uu____29681 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29681 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29684,FStar_Syntax_Syntax.Comp uu____29685) ->
                     let uu____29694 =
                       let uu___3883_29697 = problem  in
                       let uu____29700 =
                         let uu____29701 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29701
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3883_29697.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29700;
                         FStar_TypeChecker_Common.relation =
                           (uu___3883_29697.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3883_29697.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3883_29697.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3883_29697.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3883_29697.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3883_29697.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3883_29697.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3883_29697.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29694 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29702,FStar_Syntax_Syntax.Comp uu____29703) ->
                     let uu____29712 =
                       let uu___3883_29715 = problem  in
                       let uu____29718 =
                         let uu____29719 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29719
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3883_29715.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29718;
                         FStar_TypeChecker_Common.relation =
                           (uu___3883_29715.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3883_29715.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3883_29715.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3883_29715.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3883_29715.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3883_29715.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3883_29715.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3883_29715.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29712 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29720,FStar_Syntax_Syntax.GTotal uu____29721) ->
                     let uu____29730 =
                       let uu___3895_29733 = problem  in
                       let uu____29736 =
                         let uu____29737 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29737
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3895_29733.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3895_29733.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3895_29733.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29736;
                         FStar_TypeChecker_Common.element =
                           (uu___3895_29733.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3895_29733.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3895_29733.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3895_29733.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3895_29733.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3895_29733.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29730 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29738,FStar_Syntax_Syntax.Total uu____29739) ->
                     let uu____29748 =
                       let uu___3895_29751 = problem  in
                       let uu____29754 =
                         let uu____29755 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29755
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3895_29751.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3895_29751.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3895_29751.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29754;
                         FStar_TypeChecker_Common.element =
                           (uu___3895_29751.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3895_29751.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3895_29751.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3895_29751.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3895_29751.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3895_29751.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29748 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29756,FStar_Syntax_Syntax.Comp uu____29757) ->
                     let uu____29758 =
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
                     if uu____29758
                     then
                       let uu____29761 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29761 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29768 =
                            let uu____29773 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29773
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29782 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29783 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29782, uu____29783))
                             in
                          match uu____29768 with
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
                           (let uu____29791 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29791
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29799 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29799 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29802 =
                                  mklstr
                                    (fun uu____29809  ->
                                       let uu____29810 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29812 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29810 uu____29812)
                                   in
                                giveup env uu____29802 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29823 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29823 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29873 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29873 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29898 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29929  ->
                match uu____29929 with
                | (u1,u2) ->
                    let uu____29937 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29939 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29937 uu____29939))
         in
      FStar_All.pipe_right uu____29898 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29976,[])) when
          let uu____30003 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____30003 -> "{}"
      | uu____30006 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30033 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____30033
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30064 =
              FStar_List.map
                (fun uu____30078  ->
                   match uu____30078 with
                   | (msg,x) ->
                       let uu____30089 =
                         let uu____30091 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30091  in
                       Prims.op_Hat msg uu____30089) defs
               in
            FStar_All.pipe_right uu____30064 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30101 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30103 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30105 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30101 uu____30103 uu____30105 imps
  
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
                  let uu____30162 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30162
                  then
                    let uu____30170 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30172 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30170
                      (rel_to_string rel) uu____30172
                  else "TOP"  in
                let uu____30178 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30178 with
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
              let uu____30238 =
                let uu____30241 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30244  -> FStar_Pervasives_Native.Some _30244)
                  uu____30241
                 in
              FStar_Syntax_Syntax.new_bv uu____30238 t1  in
            let uu____30245 =
              let uu____30250 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30250
               in
            match uu____30245 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____30322 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30322
         then
           let uu____30327 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30327
         else ());
        (let uu____30334 =
           FStar_Util.record_time (fun uu____30341  -> solve env probs)  in
         match uu____30334 with
         | (sol,ms) ->
             ((let uu____30355 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30355
               then
                 let uu____30360 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30360
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30376 =
                     FStar_Util.record_time
                       (fun uu____30383  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30376 with
                    | ((),ms1) ->
                        ((let uu____30396 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30396
                          then
                            let uu____30401 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30401
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30415 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30415
                     then
                       let uu____30422 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30422
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
          ((let uu____30450 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30450
            then
              let uu____30455 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30455
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30463 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30463
             then
               let uu____30468 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30468
             else ());
            (let f2 =
               let uu____30474 =
                 let uu____30475 = FStar_Syntax_Util.unmeta f1  in
                 uu____30475.FStar_Syntax_Syntax.n  in
               match uu____30474 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30479 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4014_30480 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4014_30480.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4014_30480.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4014_30480.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4014_30480.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred
        * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
        -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,defer_to_tac,implicits) ->
            let uu____30532 =
              let uu____30533 =
                let uu____30534 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30535  ->
                       FStar_TypeChecker_Common.NonTrivial _30535)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30534;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30533  in
            FStar_All.pipe_left
              (fun _30542  -> FStar_Pervasives_Native.Some _30542)
              uu____30532
  
let with_guard_no_simp :
  'Auu____30552 .
    'Auu____30552 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,defer_to_tac,implicits) ->
            let uu____30601 =
              let uu____30602 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30603  -> FStar_TypeChecker_Common.NonTrivial _30603)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30602;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30601
  
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
          (let uu____30636 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30636
           then
             let uu____30641 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30643 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30641
               uu____30643
           else ());
          (let uu____30648 =
             let uu____30653 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30653
              in
           match uu____30648 with
           | (prob,wl) ->
               let g =
                 let uu____30661 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30671  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30661  in
               ((let uu____30693 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30693
                 then
                   let uu____30698 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30698
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
        let uu____30719 = try_teq true env t1 t2  in
        match uu____30719 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30724 = FStar_TypeChecker_Env.get_range env  in
              let uu____30725 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30724 uu____30725);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30733 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30733
              then
                let uu____30738 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30740 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30742 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30738
                  uu____30740 uu____30742
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
        (let uu____30766 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30766
         then
           let uu____30771 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30773 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30771
             uu____30773
         else ());
        (let uu____30778 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30778 with
         | (prob,x,wl) ->
             let g =
               let uu____30793 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30804  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30793  in
             ((let uu____30826 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30826
               then
                 let uu____30831 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30831
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30839 =
                     let uu____30840 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30840 g1  in
                   FStar_Pervasives_Native.Some uu____30839)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30862 = FStar_TypeChecker_Env.get_range env  in
          let uu____30863 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30862 uu____30863
  
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
        (let uu____30892 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30892
         then
           let uu____30897 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30899 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30897 uu____30899
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30910 =
           let uu____30917 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30917 "sub_comp"
            in
         match uu____30910 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30930 =
                 FStar_Util.record_time
                   (fun uu____30942  ->
                      let uu____30943 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30954  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30943)
                  in
               match uu____30930 with
               | (r,ms) ->
                   ((let uu____30986 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30986
                     then
                       let uu____30991 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30993 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30995 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30991 uu____30993
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30995
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
      fun uu____31033  ->
        match uu____31033 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31076 =
                 let uu____31082 =
                   let uu____31084 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31086 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31084 uu____31086
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31082)  in
               let uu____31090 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31076 uu____31090)
               in
            let equiv1 v1 v' =
              let uu____31103 =
                let uu____31108 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____31109 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31108, uu____31109)  in
              match uu____31103 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31129 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____31160 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____31160 with
                      | FStar_Syntax_Syntax.U_unif uu____31167 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31196  ->
                                    match uu____31196 with
                                    | (u,v') ->
                                        let uu____31205 = equiv1 v1 v'  in
                                        if uu____31205
                                        then
                                          let uu____31210 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____31210 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____31231 -> []))
               in
            let uu____31236 =
              let wl =
                let uu___4127_31240 = empty_worklist env  in
                {
                  attempting = (uu___4127_31240.attempting);
                  wl_deferred = (uu___4127_31240.wl_deferred);
                  wl_deferred_to_tac = (uu___4127_31240.wl_deferred_to_tac);
                  ctr = (uu___4127_31240.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4127_31240.smt_ok);
                  umax_heuristic_ok = (uu___4127_31240.umax_heuristic_ok);
                  tcenv = (uu___4127_31240.tcenv);
                  wl_implicits = (uu___4127_31240.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31259  ->
                      match uu____31259 with
                      | (lb,v1) ->
                          let uu____31266 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31266 with
                           | USolved wl1 -> ()
                           | uu____31269 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31280 =
              match uu____31280 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31292) -> true
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
                      uu____31316,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31318,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31329) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31337,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31346 -> false)
               in
            let uu____31352 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31369  ->
                      match uu____31369 with
                      | (u,v1) ->
                          let uu____31377 = check_ineq (u, v1)  in
                          if uu____31377
                          then true
                          else
                            ((let uu____31385 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31385
                              then
                                let uu____31390 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31392 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31390
                                  uu____31392
                              else ());
                             false)))
               in
            if uu____31352
            then ()
            else
              ((let uu____31402 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31402
                then
                  ((let uu____31408 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31408);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31420 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31420))
                else ());
               (let uu____31433 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31433))
  
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
        let fail1 uu____31508 =
          match uu____31508 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4204_31535 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4204_31535.attempting);
            wl_deferred = (uu___4204_31535.wl_deferred);
            wl_deferred_to_tac = (uu___4204_31535.wl_deferred_to_tac);
            ctr = (uu___4204_31535.ctr);
            defer_ok;
            smt_ok = (uu___4204_31535.smt_ok);
            umax_heuristic_ok = (uu___4204_31535.umax_heuristic_ok);
            tcenv = (uu___4204_31535.tcenv);
            wl_implicits = (uu___4204_31535.wl_implicits)
          }  in
        (let uu____31538 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31538
         then
           let uu____31543 = FStar_Util.string_of_bool defer_ok  in
           let uu____31545 = wl_to_string wl  in
           let uu____31547 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31543 uu____31545 uu____31547
         else ());
        (let g1 =
           let uu____31553 = solve_and_commit env wl fail1  in
           match uu____31553 with
           | FStar_Pervasives_Native.Some
               (uu____31562::uu____31563,uu____31564,uu____31565) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
               let uu___4221_31599 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4221_31599.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred_to_tac =
                   (FStar_List.append
                      g.FStar_TypeChecker_Common.deferred_to_tac defer_to_tac);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4221_31599.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____31605 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4226_31616 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4226_31616.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4226_31616.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4226_31616.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4226_31616.FStar_TypeChecker_Common.implicits)
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
          (let uu____31692 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31692
           then
             let uu____31697 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31697
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4240_31704 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4240_31704.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4240_31704.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4240_31704.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4240_31704.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31705 =
             let uu____31707 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31707  in
           if uu____31705
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____31719 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31720 =
                        let uu____31722 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31722
                         in
                      FStar_Errors.diag uu____31719 uu____31720)
                   else ();
                   (let vc1 =
                      let uu____31728 =
                        let uu____31732 =
                          let uu____31734 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31734  in
                        FStar_Pervasives_Native.Some uu____31732  in
                      FStar_Profiling.profile
                        (fun uu____31737  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31728 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____31741 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31742 =
                         let uu____31744 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31744
                          in
                       FStar_Errors.diag uu____31741 uu____31742)
                    else ();
                    (let uu____31750 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31750 "discharge_guard'" env vc1);
                    (let uu____31752 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31752 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____31761 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31762 =
                                 let uu____31764 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31764
                                  in
                               FStar_Errors.diag uu____31761 uu____31762)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31774 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31775 =
                                 let uu____31777 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31777
                                  in
                               FStar_Errors.diag uu____31774 uu____31775)
                            else ();
                            (let vcs =
                               let uu____31791 = FStar_Options.use_tactics ()
                                  in
                               if uu____31791
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31813  ->
                                      (let uu____31815 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31815);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31859  ->
                                               match uu____31859 with
                                               | (env1,goal,opts) ->
                                                   let uu____31875 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31875, opts)))))
                               else
                                 (let uu____31879 =
                                    let uu____31886 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31886)  in
                                  [uu____31879])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31919  ->
                                     match uu____31919 with
                                     | (env1,goal,opts) ->
                                         let uu____31929 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31929 with
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
                                                 (let uu____31940 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31941 =
                                                    let uu____31943 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31945 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31943 uu____31945
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31940 uu____31941)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31952 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31953 =
                                                    let uu____31955 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31955
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31952 uu____31953)
                                               else ();
                                               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                 use_env_range_msg env1 goal1;
                                               FStar_Options.pop ())))));
                            FStar_Pervasives_Native.Some ret_g))))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31973 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31973 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31982 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31982
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31996 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31996 with
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
        let uu____32026 = try_teq false env t1 t2  in
        match uu____32026 with
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
            let uu____32070 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32070 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32077 ->
                     let uu____32078 =
                       let uu____32079 = FStar_Syntax_Subst.compress r  in
                       uu____32079.FStar_Syntax_Syntax.n  in
                     (match uu____32078 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32084) ->
                          unresolved ctx_u'
                      | uu____32101 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32125 = acc  in
            match uu____32125 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____32144 = hd1  in
                     (match uu____32144 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____32155 = unresolved ctx_u  in
                             if uu____32155
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32166 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32166
                                     then
                                       let uu____32170 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32170
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32179 = teq_nosmt env1 t tm
                                          in
                                       match uu____32179 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4353_32189 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4353_32189.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4353_32189.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4353_32189.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4353_32189.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4353_32189.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4353_32189.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4353_32189.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4356_32191 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4356_32191.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4356_32191.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4356_32191.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                               | uu____32194 ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4361_32206 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4361_32206.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4361_32206.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4361_32206.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4361_32206.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4361_32206.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4361_32206.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4361_32206.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4361_32206.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4361_32206.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4361_32206.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4361_32206.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4361_32206.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4361_32206.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4361_32206.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4361_32206.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4361_32206.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4361_32206.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4361_32206.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4361_32206.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4361_32206.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4361_32206.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4361_32206.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4361_32206.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4361_32206.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4361_32206.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4361_32206.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4361_32206.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4361_32206.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4361_32206.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4361_32206.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4361_32206.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4361_32206.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4361_32206.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4361_32206.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4361_32206.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4361_32206.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4361_32206.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4361_32206.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4361_32206.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4361_32206.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4361_32206.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4361_32206.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4361_32206.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4361_32206.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4361_32206.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4361_32206.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4361_32206.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4366_32211 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4366_32211.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4366_32211.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4366_32211.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4366_32211.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4366_32211.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4366_32211.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4366_32211.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4366_32211.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4366_32211.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4366_32211.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4366_32211.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4366_32211.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4366_32211.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4366_32211.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4366_32211.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4366_32211.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4366_32211.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4366_32211.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4366_32211.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4366_32211.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4366_32211.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4366_32211.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4366_32211.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4366_32211.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4366_32211.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4366_32211.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4366_32211.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4366_32211.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4366_32211.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4366_32211.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4366_32211.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4366_32211.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4366_32211.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4366_32211.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4366_32211.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4366_32211.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4366_32211.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32216 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32216
                                   then
                                     let uu____32221 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32223 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32225 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32227 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32221 uu____32223 uu____32225
                                       reason uu____32227
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4372_32234  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32241 =
                                             let uu____32251 =
                                               let uu____32259 =
                                                 let uu____32261 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32263 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32265 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32261 uu____32263
                                                   uu____32265
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32259, r)
                                                in
                                             [uu____32251]  in
                                           FStar_Errors.add_errors
                                             uu____32241);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32284 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32295  ->
                                               let uu____32296 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32298 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32300 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32296 uu____32298
                                                 reason uu____32300)) env2 g1
                                         true
                                        in
                                     match uu____32284 with
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
          let uu___4384_32308 = g  in
          let uu____32309 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4384_32308.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4384_32308.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4384_32308.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4384_32308.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32309
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32324 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32324
       then
         let uu____32329 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32329
       else ());
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
      (let uu____32360 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32360
       then
         let uu____32365 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32365
       else ());
      (let solve_goals_with_tac imps tac =
         let deferred_goals =
           FStar_TypeChecker_DeferredImplicits.sort_goals env imps  in
         let guard =
           let uu___4400_32383 = g  in
           {
             FStar_TypeChecker_Common.guard_f =
               (uu___4400_32383.FStar_TypeChecker_Common.guard_f);
             FStar_TypeChecker_Common.deferred_to_tac = [];
             FStar_TypeChecker_Common.deferred =
               (uu___4400_32383.FStar_TypeChecker_Common.deferred);
             FStar_TypeChecker_Common.univ_ineqs =
               (uu___4400_32383.FStar_TypeChecker_Common.univ_ineqs);
             FStar_TypeChecker_Common.implicits = imps
           }  in
         let resolve_tac =
           match tac.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_let (uu____32390,lid::[]) ->
               let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   (FStar_Syntax_Syntax.Delta_constant_at_level
                      Prims.int_zero) FStar_Pervasives_Native.None
                  in
               let dd =
                 let uu____32398 =
                   FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                 match uu____32398 with
                 | FStar_Pervasives_Native.Some dd -> dd
                 | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                  in
               let term =
                 let uu____32404 =
                   FStar_Syntax_Syntax.lid_as_fv lid dd
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____32404  in
               term
           | uu____32405 -> failwith "Resolve_tac not found"  in
         let env1 =
           let uu___4417_32408 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___4417_32408.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___4417_32408.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___4417_32408.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___4417_32408.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___4417_32408.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___4417_32408.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___4417_32408.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___4417_32408.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___4417_32408.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___4417_32408.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___4417_32408.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___4417_32408.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___4417_32408.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___4417_32408.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___4417_32408.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___4417_32408.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___4417_32408.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___4417_32408.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___4417_32408.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___4417_32408.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___4417_32408.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___4417_32408.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___4417_32408.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___4417_32408.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___4417_32408.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___4417_32408.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___4417_32408.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___4417_32408.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___4417_32408.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___4417_32408.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___4417_32408.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___4417_32408.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___4417_32408.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___4417_32408.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___4417_32408.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___4417_32408.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___4417_32408.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___4417_32408.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___4417_32408.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___4417_32408.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___4417_32408.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___4417_32408.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___4417_32408.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___4417_32408.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___4417_32408.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___4417_32408.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___4417_32408.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac = false
           }  in
         env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1 resolve_tac
           deferred_goals
          in
       let solve_deferred_to_tactic g1 =
         let deferred = g1.FStar_TypeChecker_Common.deferred_to_tac  in
         match deferred with
         | [] -> g1
         | uu____32422 ->
             let prob_as_implicit uu____32437 =
               match uu____32437 with
               | (reason,prob) ->
                   (match prob with
                    | FStar_TypeChecker_Common.TProb tp when
                        tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ
                        ->
                        let env1 =
                          let uu___4431_32459 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4431_32459.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4431_32459.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4431_32459.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4431_32459.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4431_32459.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4431_32459.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4431_32459.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4431_32459.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4431_32459.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4431_32459.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4431_32459.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4431_32459.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4431_32459.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4431_32459.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4431_32459.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4431_32459.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4431_32459.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4431_32459.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4431_32459.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___4431_32459.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4431_32459.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4431_32459.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4431_32459.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4431_32459.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4431_32459.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4431_32459.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4431_32459.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4431_32459.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4431_32459.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___4431_32459.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4431_32459.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4431_32459.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4431_32459.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4431_32459.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4431_32459.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4431_32459.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4431_32459.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4431_32459.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4431_32459.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4431_32459.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4431_32459.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4431_32459.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4431_32459.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4431_32459.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4431_32459.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4431_32459.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4431_32459.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let env_lax =
                          let uu___4434_32461 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4434_32461.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4434_32461.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4434_32461.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___4434_32461.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4434_32461.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4434_32461.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4434_32461.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4434_32461.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4434_32461.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4434_32461.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4434_32461.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4434_32461.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4434_32461.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4434_32461.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4434_32461.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4434_32461.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4434_32461.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4434_32461.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4434_32461.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4434_32461.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4434_32461.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4434_32461.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4434_32461.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4434_32461.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4434_32461.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4434_32461.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4434_32461.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4434_32461.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4434_32461.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts = true;
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4434_32461.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4434_32461.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4434_32461.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4434_32461.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4434_32461.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4434_32461.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4434_32461.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4434_32461.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4434_32461.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4434_32461.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4434_32461.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4434_32461.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4434_32461.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4434_32461.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4434_32461.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4434_32461.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4434_32461.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let uu____32464 =
                          env1.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.lhs
                           in
                        (match uu____32464 with
                         | (uu____32475,tlhs,uu____32477) ->
                             let goal_ty =
                               let uu____32479 =
                                 env1.FStar_TypeChecker_Env.universe_of
                                   env_lax tlhs
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____32479 tlhs
                                 tp.FStar_TypeChecker_Common.lhs
                                 tp.FStar_TypeChecker_Common.rhs
                                in
                             let uu____32480 =
                               FStar_TypeChecker_Env.new_implicit_var_aux
                                 reason
                                 (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                 env1 goal_ty
                                 FStar_Syntax_Syntax.Allow_untyped
                                 FStar_Pervasives_Native.None
                                in
                             (match uu____32480 with
                              | (goal,ctx_uvar,uu____32499) ->
                                  let imp =
                                    let uu____32513 =
                                      let uu____32514 =
                                        FStar_List.hd ctx_uvar  in
                                      FStar_Pervasives_Native.fst uu____32514
                                       in
                                    {
                                      FStar_TypeChecker_Common.imp_reason =
                                        "";
                                      FStar_TypeChecker_Common.imp_uvar =
                                        uu____32513;
                                      FStar_TypeChecker_Common.imp_tm = goal;
                                      FStar_TypeChecker_Common.imp_range =
                                        ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                    }  in
                                  let sigelt =
                                    let uu____32527 =
                                      is_flex tp.FStar_TypeChecker_Common.lhs
                                       in
                                    if uu____32527
                                    then
                                      let uu____32532 =
                                        flex_uvar_head
                                          tp.FStar_TypeChecker_Common.lhs
                                         in
                                      find_user_tac_for_uvar env1 uu____32532
                                    else
                                      (let uu____32535 =
                                         is_flex
                                           tp.FStar_TypeChecker_Common.rhs
                                          in
                                       if uu____32535
                                       then
                                         let uu____32540 =
                                           flex_uvar_head
                                             tp.FStar_TypeChecker_Common.rhs
                                            in
                                         find_user_tac_for_uvar env1
                                           uu____32540
                                       else FStar_Pervasives_Native.None)
                                     in
                                  (match sigelt with
                                   | FStar_Pervasives_Native.None  ->
                                       failwith
                                         "Impossible: No tactic associated with deferred problem"
                                   | FStar_Pervasives_Native.Some se ->
                                       (imp, se))))
                    | uu____32553 ->
                        failwith "Unexpected problem deferred to tactic")
                in
             let eqs =
               FStar_List.map prob_as_implicit
                 g1.FStar_TypeChecker_Common.deferred_to_tac
                in
             let uu____32575 =
               FStar_List.fold_right
                 (fun imp  ->
                    fun uu____32607  ->
                      match uu____32607 with
                      | (more,imps) ->
                          let uu____32650 =
                            FStar_Syntax_Unionfind.find
                              (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          (match uu____32650 with
                           | FStar_Pervasives_Native.Some uu____32665 ->
                               (more, (imp :: imps))
                           | FStar_Pervasives_Native.None  ->
                               let se =
                                 find_user_tac_for_uvar env
                                   imp.FStar_TypeChecker_Common.imp_uvar
                                  in
                               (match se with
                                | FStar_Pervasives_Native.None  ->
                                    (more, (imp :: imps))
                                | FStar_Pervasives_Native.Some se1 ->
                                    let imp1 =
                                      match (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_meta
                                      with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                          a) ->
                                          let reason =
                                            let uu____32704 =
                                              FStar_Syntax_Print.term_to_string
                                                a
                                               in
                                            FStar_Util.format2 "%s::%s"
                                              uu____32704
                                              imp.FStar_TypeChecker_Common.imp_reason
                                             in
                                          let uu___4470_32707 = imp  in
                                          {
                                            FStar_TypeChecker_Common.imp_reason
                                              = reason;
                                            FStar_TypeChecker_Common.imp_uvar
                                              =
                                              (uu___4470_32707.FStar_TypeChecker_Common.imp_uvar);
                                            FStar_TypeChecker_Common.imp_tm =
                                              (uu___4470_32707.FStar_TypeChecker_Common.imp_tm);
                                            FStar_TypeChecker_Common.imp_range
                                              =
                                              (uu___4470_32707.FStar_TypeChecker_Common.imp_range)
                                          }
                                      | uu____32708 -> imp  in
                                    (((imp1, se1) :: more), imps))))
                 g1.FStar_TypeChecker_Common.implicits ([], [])
                in
             (match uu____32575 with
              | (more,imps) ->
                  let bucketize is =
                    let map1 = FStar_Util.smap_create (Prims.of_int (17))  in
                    FStar_List.iter
                      (fun uu____32804  ->
                         match uu____32804 with
                         | (i,s) ->
                             let uu____32811 =
                               FStar_Syntax_Util.lid_of_sigelt s  in
                             (match uu____32811 with
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Unexpected: tactic without a name"
                              | FStar_Pervasives_Native.Some l ->
                                  let uu____32816 =
                                    FStar_Util.smap_try_find map1
                                      l.FStar_Ident.nsstr
                                     in
                                  (match uu____32816 with
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Util.smap_add map1
                                         l.FStar_Ident.nsstr ([i], s)
                                   | FStar_Pervasives_Native.Some (is1,s1) ->
                                       (FStar_Util.smap_remove map1
                                          l.FStar_Ident.nsstr;
                                        FStar_Util.smap_add map1
                                          l.FStar_Ident.nsstr
                                          ((i :: is1), s1))))) is;
                    FStar_Util.smap_fold map1
                      (fun uu____32863  -> fun is1  -> fun out  -> is1 :: out)
                      []
                     in
                  let buckets = bucketize (FStar_List.append eqs more)  in
                  (FStar_List.iter
                     (fun uu____32904  ->
                        match uu____32904 with
                        | (imps1,sigel) -> solve_goals_with_tac imps1 sigel)
                     buckets;
                   (let uu___4501_32911 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___4501_32911.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac = [];
                      FStar_TypeChecker_Common.deferred =
                        (uu___4501_32911.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___4501_32911.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = imps
                    })))
          in
       let g1 = solve_deferred_constraints env g  in
       let g2 = solve_deferred_to_tactic g1  in
       (let uu____32920 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ResolveImplicitsHook")
           in
        if uu____32920
        then
          let uu____32925 = guard_to_string env g2  in
          FStar_Util.print1
            "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
            uu____32925
        else ());
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____32931 = discharge_guard env g3  in
            FStar_All.pipe_left (fun a2  -> ()) uu____32931
        | imp::uu____32933 ->
            let uu____32936 =
              let uu____32942 =
                let uu____32944 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____32946 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____32944 uu____32946
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32942)
               in
            FStar_Errors.raise_error uu____32936
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32966 = teq env t1 t2  in
        force_trivial_guard env uu____32966
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32985 = teq_nosmt env t1 t2  in
        match uu____32985 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4524_33004 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4524_33004.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4524_33004.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4524_33004.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4524_33004.FStar_TypeChecker_Common.implicits)
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
        (let uu____33040 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____33040
         then
           let uu____33045 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____33047 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____33045
             uu____33047
         else ());
        (let uu____33052 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____33052 with
         | (prob,x,wl) ->
             let g =
               let uu____33071 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____33082  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____33071  in
             ((let uu____33104 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____33104
               then
                 let uu____33109 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____33111 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____33113 =
                   let uu____33115 = FStar_Util.must g  in
                   guard_to_string env uu____33115  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____33109 uu____33111 uu____33113
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
        let uu____33152 = check_subtyping env t1 t2  in
        match uu____33152 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____33171 =
              let uu____33172 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____33172 g  in
            FStar_Pervasives_Native.Some uu____33171
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33191 = check_subtyping env t1 t2  in
        match uu____33191 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____33210 =
              let uu____33211 =
                let uu____33212 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____33212]  in
              FStar_TypeChecker_Env.close_guard env uu____33211 g  in
            FStar_Pervasives_Native.Some uu____33210
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____33250 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____33250
         then
           let uu____33255 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____33257 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____33255
             uu____33257
         else ());
        (let uu____33262 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____33262 with
         | (prob,x,wl) ->
             let g =
               let uu____33277 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____33288  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____33277  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____33313 =
                      let uu____33314 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____33314]  in
                    FStar_TypeChecker_Env.close_guard env uu____33313 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33355 = subtype_nosmt env t1 t2  in
        match uu____33355 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  