open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____25 =
        let uu____26 =
          let uu____43 =
            FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          let uu____46 =
            let uu____57 = FStar_Syntax_Syntax.iarg t  in
            let uu____66 =
              let uu____77 =
                let uu____86 =
                  let uu____87 =
                    let uu____88 =
                      let uu____89 =
                        let uu____95 =
                          let uu____97 = FStar_Syntax_Print.lid_to_string lid
                             in
                          Prims.op_Hat "Not yet implemented:" uu____97  in
                        (uu____95, FStar_Range.dummyRange)  in
                      FStar_Const.Const_string uu____89  in
                    FStar_Syntax_Syntax.Tm_constant uu____88  in
                  FStar_Syntax_Syntax.mk uu____87 FStar_Range.dummyRange  in
                FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____86  in
              [uu____77]  in
            uu____57 :: uu____66  in
          (uu____43, uu____46)  in
        FStar_Syntax_Syntax.Tm_app uu____26  in
      FStar_Syntax_Syntax.mk uu____25 FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____163 = FStar_Syntax_Util.arrow_formals t  in
        match uu____163 with
        | ([],t1) ->
            let b =
              let uu____190 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____190  in
            let uu____198 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____198 FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____219 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____219 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____223 =
          let uu____228 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____228  in
        {
          FStar_Syntax_Syntax.lbname = uu____223;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        }  in
      lb
  
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x  -> x 
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1  ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
  
let as_pair :
  'Auu____250 . 'Auu____250 Prims.list -> ('Auu____250 * 'Auu____250) =
  fun uu___0_261  ->
    match uu___0_261 with
    | a::b::[] -> (a, b)
    | uu____266 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_281  ->
    match uu___1_281 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____284 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____293 = FStar_Syntax_Subst.compress x  in
    match uu____293 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____297;
        FStar_Syntax_Syntax.vars = uu____298;_} ->
        let uu____301 =
          let uu____303 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____303  in
        (match uu____301 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.PpxDerivingYoJson" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingYoJson
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | "FStar.Pervasives.CAbstractStruct" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.CAbstract
         | "FStar.Pervasives.CIfDef" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CIfDef
         | "FStar.Pervasives.CMacro" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CMacro
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated "")
         | uu____316 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____319;
             FStar_Syntax_Syntax.vars = uu____320;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____322));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____323;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____324;_},uu____325)::[]);
        FStar_Syntax_Syntax.pos = uu____326;
        FStar_Syntax_Syntax.vars = uu____327;_} ->
        let uu____370 =
          let uu____372 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____372  in
        (match uu____370 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CConst s)
         | "FStar.Pervasives.CCConv" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CCConv s)
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated s)
         | uu____382 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____384));
        FStar_Syntax_Syntax.pos = uu____385;
        FStar_Syntax_Syntax.vars = uu____386;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____391));
        FStar_Syntax_Syntax.pos = uu____392;
        FStar_Syntax_Syntax.vars = uu____393;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____398));
        FStar_Syntax_Syntax.pos = uu____399;
        FStar_Syntax_Syntax.vars = uu____400;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____406);
        FStar_Syntax_Syntax.pos = uu____407;
        FStar_Syntax_Syntax.vars = uu____408;_} -> extract_meta x1
    | uu____415 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____435 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____435) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____477  ->
             match uu____477 with
             | (bv,uu____488) ->
                 let uu____489 =
                   let uu____490 =
                     let uu____493 =
                       let uu____494 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____494  in
                     FStar_Pervasives_Native.Some uu____493  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____490  in
                 let uu____496 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____489, uu____496)) env bs
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee  -> match projectee with | { dname; dtyp;_} -> dname 
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | { dname; dtyp;_} -> dtyp 
type inductive_family =
  {
  ifv: FStar_Syntax_Syntax.fv ;
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }
let (__proj__Mkinductive_family__item__ifv :
  inductive_family -> FStar_Syntax_Syntax.fv) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ifv
  
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iname
  
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iparams
  
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ityp
  
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> idatas
  
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iquals
  
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee  ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> imetadata
  
let (print_ifamily : inductive_family -> unit) =
  fun i  ->
    let uu____697 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____699 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____702 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____704 =
      let uu____706 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____720 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____722 =
                  let uu____724 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____724  in
                Prims.op_Hat uu____720 uu____722))
         in
      FStar_All.pipe_right uu____706 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____697 uu____699 uu____702
      uu____704
  
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        let uu____769 =
          FStar_Util.fold_map
            (fun env1  ->
               fun se  ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l,us,bs,t,_mut_i,datas) ->
                     let uu____820 = FStar_Syntax_Subst.open_univ_vars us t
                        in
                     (match uu____820 with
                      | (_us,t1) ->
                          let uu____833 = FStar_Syntax_Subst.open_term bs t1
                             in
                          (match uu____833 with
                           | (bs1,t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1  ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d,us1,t3,l',nparams,uu____879)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____886 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3
                                                in
                                             (match uu____886 with
                                              | (_us1,t4) ->
                                                  let uu____895 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4
                                                     in
                                                  (match uu____895 with
                                                   | (bs',body) ->
                                                       let uu____910 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs'
                                                          in
                                                       (match uu____910 with
                                                        | (bs_params,rest) ->
                                                            let subst1 =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1001
                                                                    ->
                                                                   fun
                                                                    uu____1002
                                                                     ->
                                                                    match 
                                                                    (uu____1001,
                                                                    uu____1002)
                                                                    with
                                                                    | 
                                                                    ((b',uu____1028),
                                                                    (b,uu____1030))
                                                                    ->
                                                                    let uu____1051
                                                                    =
                                                                    let uu____1058
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                    (b',
                                                                    uu____1058)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1051)
                                                                bs_params bs1
                                                               in
                                                            let t5 =
                                                              let uu____1064
                                                                =
                                                                let uu____1065
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1065
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____1064
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1)
                                                               in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1068 -> []))
                                  in
                               let metadata =
                                 let uu____1072 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs
                                    in
                                 let uu____1075 =
                                   FStar_List.choose flag_of_qual quals  in
                                 FStar_List.append uu____1072 uu____1075  in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None
                                  in
                               let env2 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv
                                  in
                               (env2,
                                 [{
                                    ifv = fv;
                                    iname = l;
                                    iparams = bs1;
                                    ityp = t2;
                                    idatas = datas1;
                                    iquals =
                                      (se.FStar_Syntax_Syntax.sigquals);
                                    imetadata = metadata
                                  }])))
                 | uu____1082 -> (env1, [])) env ses
           in
        match uu____769 with
        | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs: FStar_Extraction_ML_UEnv.tydef Prims.list ;
  iface_type_names: FStar_Syntax_Syntax.fv Prims.list }
let (__proj__Mkiface__item__iface_module_name :
  iface -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_module_name
  
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_bindings
  
let (__proj__Mkiface__item__iface_tydefs :
  iface -> FStar_Extraction_ML_UEnv.tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
  
let (__proj__Mkiface__item__iface_type_names :
  iface -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee  ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_type_names
  
let (empty_iface : iface) =
  {
    iface_module_name = ([], "");
    iface_bindings = [];
    iface_tydefs = [];
    iface_type_names = []
  } 
let (iface_of_bindings :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list
    -> iface)
  =
  fun fvs  ->
    let uu___216_1262 = empty_iface  in
    {
      iface_module_name = (uu___216_1262.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___216_1262.iface_tydefs);
      iface_type_names = (uu___216_1262.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___219_1273 = empty_iface  in
    let uu____1274 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___219_1273.iface_module_name);
      iface_bindings = (uu___219_1273.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____1274
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___223_1289 = empty_iface  in
    {
      iface_module_name = (uu___223_1289.iface_module_name);
      iface_bindings = (uu___223_1289.iface_bindings);
      iface_tydefs = (uu___223_1289.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____1301 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____1301;
        iface_bindings =
          (FStar_List.append if1.iface_bindings if2.iface_bindings);
        iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStar_List.append if1.iface_type_names if2.iface_type_names)
      }
  
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs  -> FStar_List.fold_right iface_union ifs empty_iface 
let (mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath -> Prims.string) =
  fun p  ->
    FStar_String.concat ". "
      (FStar_List.append (FStar_Pervasives_Native.fst p)
         [FStar_Pervasives_Native.snd p])
  
let tscheme_to_string :
  'Auu____1346 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____1346 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
  =
  fun cm  ->
    fun ts  ->
      FStar_Extraction_ML_Code.string_of_mlty cm
        (FStar_Pervasives_Native.snd ts)
  
let (print_exp_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.exp_binding -> Prims.string)
  =
  fun cm  ->
    fun e  ->
      let uu____1378 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____1380 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____1382 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1378 uu____1380
        uu____1382
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____1400  ->
      match uu____1400 with
      | (fv,exp_binding) ->
          let uu____1408 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____1410 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____1408 uu____1410
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____1425 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____1427 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____1425 uu____1427
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____1445 =
      let uu____1447 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____1447 (FStar_String.concat "\n")  in
    let uu____1461 =
      let uu____1463 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____1463 (FStar_String.concat "\n")  in
    let uu____1473 =
      let uu____1475 = FStar_List.map print_type_name iface1.iface_type_names
         in
      FStar_All.pipe_right uu____1475 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1445 uu____1461
      uu____1473
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___2_1508  ->
           match uu___2_1508 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____1525 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____1530 =
      let uu____1532 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____1532 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1530
  
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env  ->
    fun quals  ->
      fun attrs  ->
        fun lb  ->
          let uu____1592 =
            let uu____1601 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____1601 with
            | (tcenv,uu____1619,def_typ) ->
                let uu____1625 = as_pair def_typ  in (tcenv, uu____1625)
             in
          match uu____1592 with
          | (tcenv,(lbdef,lbtyp)) ->
              let lbtyp1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant] tcenv lbtyp
                 in
              let lbdef1 =
                FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1
                 in
              let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let def =
                let uu____1656 =
                  let uu____1657 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____1657 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____1656 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1665 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1684 -> def  in
              let uu____1685 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1696) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1721 -> ([], def1)  in
              (match uu____1685 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1741  ->
                          match uu___3_1741 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____1744 -> false) quals
                      in
                   let uu____1746 = binders_as_mlty_binders env bs  in
                   (match uu____1746 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____1773 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____1773
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____1778 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_1785  ->
                                    match uu___4_1785 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____1787 -> true
                                    | uu____1793 -> false))
                             in
                          if uu____1778
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____1807 = extract_metadata attrs  in
                          let uu____1810 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____1807 uu____1810  in
                        let td =
                          let uu____1833 = lident_as_mlsymbol lid  in
                          (assumed, uu____1833, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____1845 =
                            let uu____1846 =
                              let uu____1847 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____1847
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____1846  in
                          [uu____1845;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____1848 =
                          let uu____1853 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___5_1859  ->
                                    match uu___5_1859 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____1863 -> false))
                             in
                          if uu____1853
                          then
                            let uu____1870 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____1870, (iface_of_type_names [fv]))
                          else
                            (let uu____1873 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____1873 with
                             | (env2,tydef) ->
                                 let uu____1884 = iface_of_tydefs [tydef]  in
                                 (env2, uu____1884))
                           in
                        (match uu____1848 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_let_rec_type :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env  ->
    fun quals  ->
      fun attrs  ->
        fun lb  ->
          let lbtyp =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv
              lb.FStar_Syntax_Syntax.lbtyp
             in
          let uu____1943 = FStar_Syntax_Util.arrow_formals lbtyp  in
          match uu____1943 with
          | (bs,uu____1959) ->
              let uu____1964 = binders_as_mlty_binders env bs  in
              (match uu____1964 with
               | (env1,ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                      in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top  in
                   let metadata =
                     let uu____1996 = extract_metadata attrs  in
                     let uu____1999 = FStar_List.choose flag_of_qual quals
                        in
                     FStar_List.append uu____1996 uu____1999  in
                   let assumed = false  in
                   let td =
                     let uu____2025 = lident_as_mlsymbol lid  in
                     (assumed, uu____2025, FStar_Pervasives_Native.None,
                       ml_bs, metadata,
                       (FStar_Pervasives_Native.Some
                          (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                      in
                   let def =
                     let uu____2038 =
                       let uu____2039 =
                         let uu____2040 = FStar_Ident.range_of_lid lid  in
                         FStar_Extraction_ML_Util.mlloc_of_range uu____2040
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____2039  in
                     [uu____2038; FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                   let uu____2041 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (match uu____2041 with
                    | (env2,tydef) ->
                        let iface1 = iface_of_tydefs [tydef]  in
                        (env2, iface1, def)))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____2122 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2122
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____2129 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____2129 with | (env2,uu____2148,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____2187 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____2187 with
        | (env_iparams,vars) ->
            let uu____2215 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____2215 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____2279,t,uu____2281,uu____2282,uu____2283);
            FStar_Syntax_Syntax.sigrng = uu____2284;
            FStar_Syntax_Syntax.sigquals = uu____2285;
            FStar_Syntax_Syntax.sigmeta = uu____2286;
            FStar_Syntax_Syntax.sigattrs = uu____2287;
            FStar_Syntax_Syntax.sigopts = uu____2288;_}::[],uu____2289),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____2310 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____2310 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____2343),quals) ->
          let uu____2357 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____2357
          then (env, empty_iface)
          else
            (let uu____2366 = bundle_as_inductive_families env ses quals  in
             match uu____2366 with
             | (env1,ifams) ->
                 let uu____2383 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____2383 with
                  | (env2,td) ->
                      let uu____2424 =
                        let uu____2425 =
                          let uu____2426 =
                            FStar_List.map (fun x  -> x.ifv) ifams  in
                          iface_of_type_names uu____2426  in
                        iface_union uu____2425
                          (iface_of_bindings (FStar_List.flatten td))
                         in
                      (env2, uu____2424)))
      | uu____2435 -> failwith "Unexpected signature element"
  
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.univ_name Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1
                Prims.list))
  =
  fun g  ->
    fun lid  ->
      fun quals  ->
        fun attrs  ->
          fun univs1  ->
            fun t  ->
              let uu____2510 =
                let uu____2512 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___6_2518  ->
                          match uu___6_2518 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____2521 -> false))
                   in
                Prims.op_Negation uu____2512  in
              if uu____2510
              then (g, empty_iface, [])
              else
                (let uu____2536 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2536 with
                 | (bs,uu____2552) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____2559 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____2559;
                         FStar_Syntax_Syntax.lbattrs = attrs;
                         FStar_Syntax_Syntax.lbpos =
                           (t.FStar_Syntax_Syntax.pos)
                       }  in
                     extract_typ_abbrev g quals attrs lb)
  
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv * iface *
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun ed  ->
      let extend_env g1 lid ml_name tm tysc =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let uu____2622 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____2622 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____2644 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2644
              then FStar_Util.print1 "Mangled name: %s\n" mangled_name
              else ());
             (let lb =
                {
                  FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                  FStar_Extraction_ML_Syntax.mllb_tysc =
                    FStar_Pervasives_Native.None;
                  FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                  FStar_Extraction_ML_Syntax.mllb_def = tm;
                  FStar_Extraction_ML_Syntax.mllb_meta = [];
                  FStar_Extraction_ML_Syntax.print_typ = false
                }  in
              (g2, (iface_of_bindings [(fv, exp_binding)]),
                (FStar_Extraction_ML_Syntax.MLM_Let
                   (FStar_Extraction_ML_Syntax.NonRec, [lb])))))
         in
      let rec extract_fv tm =
        (let uu____2680 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2680
         then
           let uu____2685 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2685
         else ());
        (let uu____2690 =
           let uu____2691 = FStar_Syntax_Subst.compress tm  in
           uu____2691.FStar_Syntax_Syntax.n  in
         match uu____2690 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2699) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____2706 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____2706 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2711;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2712;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____2714;_} ->
                  let uu____2717 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____2717, tysc))
         | uu____2718 ->
             let uu____2719 =
               let uu____2721 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____2723 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2721 uu____2723
                in
             failwith uu____2719)
         in
      let extract_action g1 a =
        (let uu____2751 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____2751
         then
           let uu____2756 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____2758 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____2756
             uu____2758
         else ());
        (let uu____2763 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____2763 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____2783 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____2783  in
             let lb =
               FStar_Syntax_Syntax.mk_lb
                 (lbname, (a.FStar_Syntax_Syntax.action_univs),
                   FStar_Parser_Const.effect_Tot_lid,
                   (a.FStar_Syntax_Syntax.action_typ),
                   (a.FStar_Syntax_Syntax.action_defn), [],
                   ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                in
             let lbs = (false, [lb])  in
             let action_lb =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                in
             let uu____2813 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____2813 with
              | (a_let,uu____2829,ty) ->
                  ((let uu____2832 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____2832
                    then
                      let uu____2837 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____2837
                    else ());
                   (let uu____2842 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____2865,mllb::[]),uu____2867) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____2907 -> failwith "Impossible"  in
                    match uu____2842 with
                    | (exp,tysc) ->
                        ((let uu____2945 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____2945
                          then
                            ((let uu____2951 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____2951);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____2967 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____2967 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____2989 =
        let uu____2996 =
          let uu____3001 =
            let uu____3004 =
              let uu____3013 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr  in
              FStar_All.pipe_right uu____3013 FStar_Util.must  in
            FStar_All.pipe_right uu____3004 FStar_Pervasives_Native.snd  in
          extract_fv uu____3001  in
        match uu____2996 with
        | (return_tm,ty_sc) ->
            let uu____3082 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____3082 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____2989 with
      | (g1,return_iface,return_decl) ->
          let uu____3107 =
            let uu____3114 =
              let uu____3119 =
                let uu____3122 =
                  let uu____3131 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr
                     in
                  FStar_All.pipe_right uu____3131 FStar_Util.must  in
                FStar_All.pipe_right uu____3122 FStar_Pervasives_Native.snd
                 in
              extract_fv uu____3119  in
            match uu____3114 with
            | (bind_tm,ty_sc) ->
                let uu____3200 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____3200 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____3107 with
           | (g2,bind_iface,bind_decl) ->
               let uu____3225 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____3225 with
                | (g3,actions) ->
                    let uu____3262 = FStar_List.unzip actions  in
                    (match uu____3262 with
                     | (actions_iface,actions1) ->
                         let uu____3289 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____3289, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_let_rec_types :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * iface *
          FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun se  ->
    fun env  ->
      fun lbs  ->
        let uu____3320 =
          FStar_Util.for_some
            (fun lb  ->
               let uu____3325 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp
                  in
               Prims.op_Negation uu____3325) lbs
           in
        if uu____3320
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3348 =
             FStar_List.fold_left
               (fun uu____3383  ->
                  fun lb  ->
                    match uu____3383 with
                    | (env1,iface_opt,impls) ->
                        let uu____3424 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb
                           in
                        (match uu____3424 with
                         | (env2,iface1,impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3458 = iface_union iface' iface1
                                      in
                                   FStar_Pervasives_Native.Some uu____3458
                                in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs
              in
           match uu____3348 with
           | (env1,iface_opt,impls) ->
               let uu____3498 = FStar_Option.get iface_opt  in
               let uu____3499 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten
                  in
               (env1, uu____3498, uu____3499))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3531 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3540 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3557 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3576 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____3576 with | (env,iface1,uu____3591) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3597) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3606 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____3606 with | (env,iface1,uu____3621) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____3627) when
          FStar_Util.for_some
            (fun lb  ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3640 = extract_let_rec_types se g lbs  in
          (match uu____3640 with | (env,iface1,uu____3655) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____3666 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3672 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____3672)
             in
          if uu____3666
          then
            let uu____3679 =
              let uu____3690 =
                let uu____3691 =
                  let uu____3694 = always_fail lid t  in [uu____3694]  in
                (false, uu____3691)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3690  in
            (match uu____3679 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____3720) ->
          let uu____3725 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____3725 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____3754 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____3755 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3762 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3763 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3776 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____3789 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____3801 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3820 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____3820
          then
            let uu____3833 = extract_reifiable_effect g ed  in
            (match uu____3833 with | (env,iface1,uu____3848) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3870 = FStar_Options.interactive ()  in
      if uu____3870
      then (g, empty_iface)
      else
        (let uu____3879 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___621_3883 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___621_3883.iface_bindings);
             iface_tydefs = (uu___621_3883.iface_tydefs);
             iface_type_names = (uu___621_3883.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____3901  ->
                fun se  ->
                  match uu____3901 with
                  | (g1,iface2) ->
                      let uu____3913 = extract_sigelt_iface g1 se  in
                      (match uu____3913 with
                       | (g2,iface') ->
                           let uu____3924 = iface_union iface2 iface'  in
                           (g2, uu____3924))) (g, iface1) decls
            in
         (let uu____3926 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____3926);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____3943 = FStar_Options.debug_any ()  in
      if uu____3943
      then
        let uu____3950 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____3950
          (fun uu____3958  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let mlident_map =
        FStar_List.fold_left
          (fun acc  ->
             fun uu____3988  ->
               match uu____3988 with
               | (uu____3999,x) ->
                   FStar_Util.psmap_add acc
                     x.FStar_Extraction_ML_UEnv.exp_b_name "")
          g.FStar_Extraction_ML_UEnv.env_mlident_map iface1.iface_bindings
         in
      let uu___644_4003 = g  in
      let uu____4004 =
        let uu____4007 =
          FStar_List.map (fun _4014  -> FStar_Extraction_ML_UEnv.Fv _4014)
            iface1.iface_bindings
           in
        FStar_List.append uu____4007 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___644_4003.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____4004;
        FStar_Extraction_ML_UEnv.env_mlident_map = mlident_map;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___644_4003.FStar_Extraction_ML_UEnv.currentModule)
      }
  
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____4092 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4092
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____4100 =
            let uu____4101 =
              let uu____4104 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____4104  in
            uu____4101.FStar_Syntax_Syntax.n  in
          match uu____4100 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____4109) ->
              FStar_List.map
                (fun uu____4142  ->
                   match uu____4142 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4151;
                        FStar_Syntax_Syntax.sort = uu____4152;_},uu____4153)
                       -> ppname.FStar_Ident.idText) bs
          | uu____4161 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____4169 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____4169 with
        | (env2,uu____4196,uu____4197) ->
            let uu____4200 =
              let uu____4213 = lident_as_mlsymbol ctor.dname  in
              let uu____4215 =
                let uu____4223 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____4223  in
              (uu____4213, uu____4215)  in
            (env2, uu____4200)
         in
      let extract_one_family env1 ind =
        let uu____4284 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____4284 with
        | (env_iparams,vars) ->
            let uu____4328 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____4328 with
             | (env2,ctors) ->
                 let uu____4435 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____4435 with
                  | (indices,uu____4469) ->
                      let ml_params =
                        let uu____4478 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____4504  ->
                                    let uu____4512 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____4512))
                           in
                        FStar_List.append vars uu____4478  in
                      let tbody =
                        let uu____4517 =
                          FStar_Util.find_opt
                            (fun uu___7_4522  ->
                               match uu___7_4522 with
                               | FStar_Syntax_Syntax.RecordType uu____4524 ->
                                   true
                               | uu____4534 -> false) ind.iquals
                           in
                        match uu____4517 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____4546 = FStar_List.hd ctors  in
                            (match uu____4546 with
                             | (uu____4571,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____4615  ->
                                          match uu____4615 with
                                          | (uu____4626,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____4631 =
                                                lident_as_mlsymbol lid  in
                                              (uu____4631, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____4634 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____4637 =
                        let uu____4660 = lident_as_mlsymbol ind.iname  in
                        (false, uu____4660, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____4637)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____4705,t,uu____4707,uu____4708,uu____4709);
            FStar_Syntax_Syntax.sigrng = uu____4710;
            FStar_Syntax_Syntax.sigquals = uu____4711;
            FStar_Syntax_Syntax.sigmeta = uu____4712;
            FStar_Syntax_Syntax.sigattrs = uu____4713;
            FStar_Syntax_Syntax.sigopts = uu____4714;_}::[],uu____4715),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____4736 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____4736 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____4789),quals) ->
          let uu____4803 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr
             in
          if uu____4803
          then (env, [])
          else
            (let uu____4816 = bundle_as_inductive_families env ses quals  in
             match uu____4816 with
             | (env1,ifams) ->
                 let uu____4835 =
                   FStar_Util.fold_map extract_one_family env1 ifams  in
                 (match uu____4835 with
                  | (env2,td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____4944 -> failwith "Unexpected signature element"
  
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let plugin_with_arity attrs =
        FStar_Util.find_map attrs
          (fun t  ->
             let uu____5002 = FStar_Syntax_Util.head_and_args t  in
             match uu____5002 with
             | (head1,args) ->
                 let uu____5050 =
                   let uu____5052 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____5052  in
                 if uu____5050
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____5071));
                         FStar_Syntax_Syntax.pos = uu____5072;
                         FStar_Syntax_Syntax.vars = uu____5073;_},uu____5074)::[]
                        ->
                        let uu____5113 =
                          let uu____5117 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____5117  in
                        FStar_Pervasives_Native.Some uu____5113
                    | uu____5123 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____5138 =
        let uu____5140 = FStar_Options.codegen ()  in
        uu____5140 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)  in
      if uu____5138
      then []
      else
        (let uu____5150 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____5150 with
         | FStar_Pervasives_Native.None  -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                       in
                    let fv_lid1 =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                       in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
                    let ml_name_str =
                      let uu____5192 =
                        let uu____5193 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5193  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5192  in
                    let uu____5195 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____5195 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin) ->
                        let uu____5228 =
                          if plugin
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____5228 with
                         | (register,args) ->
                             let h =
                               let uu____5265 =
                                 let uu____5266 =
                                   let uu____5267 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____5267
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____5266
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____5265
                                in
                             let arity1 =
                               let uu____5269 =
                                 let uu____5270 =
                                   let uu____5282 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____5282, FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5270
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5269
                                in
                             let app =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (h,
                                      (FStar_List.append
                                         [w ml_name_str; w arity1] args)))
                                in
                             [FStar_Extraction_ML_Syntax.MLM_Top app])
                    | FStar_Pervasives_Native.None  -> []  in
                  FStar_List.collect mk_registration
                    (FStar_Pervasives_Native.snd lbs)
              | uu____5311 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5339 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5339);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5348 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5357 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5374 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5391 = extract_reifiable_effect g ed  in
           (match uu____5391 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5415 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5429 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5449 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5455 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____5455 with | (env,uu____5471,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____5480) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5489 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____5489 with | (env,uu____5505,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true ,lbs),uu____5514) when
           FStar_Util.for_some
             (fun lb  ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5527 = extract_let_rec_types se g lbs  in
           (match uu____5527 with | (env,uu____5543,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____5552) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____5563 =
             let uu____5572 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____5572 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____5601) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____5563 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___878_5687 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___878_5687.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___878_5687.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___878_5687.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___878_5687.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___878_5687.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___878_5687.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____5696 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____5696)  in
                let uu____5714 =
                  let uu____5721 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5721  in
                (match uu____5714 with
                 | (ml_let,uu____5738,uu____5739) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____5748) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____5765 =
                            FStar_List.fold_left2
                              (fun uu____5791  ->
                                 fun ml_lb  ->
                                   fun uu____5793  ->
                                     match (uu____5791, uu____5793) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____5815;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____5817;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____5818;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____5819;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____5820;_})
                                         ->
                                         let uu____5845 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____5845
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5862 =
                                                let uu____5865 =
                                                  FStar_Util.right lbname  in
                                                uu____5865.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____5862.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____5869 =
                                                let uu____5870 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____5870.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____5869 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5875,{
                                                                FStar_Syntax_Syntax.n
                                                                  =
                                                                  FStar_Syntax_Syntax.Comp
                                                                  {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5876;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____5878;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5879;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____5880;_};
                                                                FStar_Syntax_Syntax.pos
                                                                  =
                                                                  uu____5881;
                                                                FStar_Syntax_Syntax.vars
                                                                  =
                                                                  uu____5882;_})
                                                  when
                                                  let uu____5917 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____5917 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____5921 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___926_5926 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___926_5926.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___926_5926.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___926_5926.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___926_5926.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___926_5926.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____5927 =
                                              let uu____5932 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___8_5939  ->
                                                        match uu___8_5939
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____5941 ->
                                                            true
                                                        | uu____5947 -> false))
                                                 in
                                              if uu____5932
                                              then
                                                let mname =
                                                  let uu____5963 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5963
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____5972 =
                                                  let uu____5980 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____5981 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____5980 mname
                                                    uu____5981
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____5972 with
                                                | (env1,uu____5988,uu____5989)
                                                    ->
                                                    (env1,
                                                      (let uu___939_5993 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___939_5993.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___939_5993.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___939_5993.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___939_5993.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___939_5993.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6000 =
                                                   let uu____6008 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6008
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____6000 with
                                                 | (env1,uu____6015,uu____6016)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____5927 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____5765 with
                           | (g1,ml_lbs') ->
                               let uu____6046 =
                                 let uu____6049 =
                                   let uu____6052 =
                                     let uu____6053 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6053
                                      in
                                   [uu____6052;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____6056 = maybe_register_plugin g1 se
                                    in
                                 FStar_List.append uu____6049 uu____6056  in
                               (g1, uu____6046))
                      | uu____6061 ->
                          let uu____6062 =
                            let uu____6064 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6064
                             in
                          failwith uu____6062)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____6074,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____6079 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6085 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____6085)
              in
           if uu____6079
           then
             let always_fail1 =
               let uu___959_6095 = se  in
               let uu____6096 =
                 let uu____6097 =
                   let uu____6104 =
                     let uu____6105 =
                       let uu____6108 = always_fail lid t  in [uu____6108]
                        in
                     (false, uu____6105)  in
                   (uu____6104, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____6097  in
               {
                 FStar_Syntax_Syntax.sigel = uu____6096;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___959_6095.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___959_6095.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___959_6095.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___959_6095.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___959_6095.FStar_Syntax_Syntax.sigopts)
               }  in
             let uu____6115 = extract_sig g always_fail1  in
             (match uu____6115 with
              | (g1,mlm) ->
                  let uu____6134 =
                    FStar_Util.find_map quals
                      (fun uu___9_6139  ->
                         match uu___9_6139 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6143 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____6134 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6151 =
                         let uu____6154 =
                           let uu____6155 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6155  in
                         let uu____6156 =
                           let uu____6159 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____6159]  in
                         uu____6154 :: uu____6156  in
                       (g1, uu____6151)
                   | uu____6162 ->
                       let uu____6165 =
                         FStar_Util.find_map quals
                           (fun uu___10_6171  ->
                              match uu___10_6171 with
                              | FStar_Syntax_Syntax.Projector (l,uu____6175)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6176 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____6165 with
                        | FStar_Pervasives_Native.Some uu____6183 -> (g1, [])
                        | uu____6186 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____6196 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____6196 with
            | (ml_main,uu____6210,uu____6211) ->
                let uu____6212 =
                  let uu____6215 =
                    let uu____6216 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____6216  in
                  [uu____6215; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____6212))
       | FStar_Syntax_Syntax.Sig_assume uu____6219 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6228 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6231 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6246 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      let uu____6286 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1002_6290 = g  in
        let uu____6291 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____6291;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1002_6290.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.env_mlident_map =
            (uu___1002_6290.FStar_Extraction_ML_UEnv.env_mlident_map);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1002_6290.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1002_6290.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____6292 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____6311 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____6311
               then
                 let nm =
                   let uu____6322 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____6322 (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____6339 = FStar_Util.format1 "---Extracted {%s}" nm
                      in
                   FStar_Util.measure_execution_time uu____6339
                     (fun uu____6349  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____6292 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____6371 = FStar_Options.codegen ()  in
            uu____6371 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____6386 =
                let uu____6388 = FStar_Options.silent ()  in
                Prims.op_Negation uu____6388  in
              if uu____6386
              then
                let uu____6391 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____6391
              else ());
             (g2,
               (FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.MLLib
                     [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                        (FStar_Extraction_ML_Syntax.MLLib []))]))))
          else (g2, FStar_Pervasives_Native.None)
  
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun m  ->
      (let uu____6466 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____6466);
      (let uu____6469 =
         let uu____6471 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____6471  in
       if uu____6469
       then
         let uu____6474 =
           let uu____6476 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6476
            in
         failwith uu____6474
       else ());
      (let uu____6481 = FStar_Options.interactive ()  in
       if uu____6481
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____6501 = FStar_Options.debug_any ()  in
            if uu____6501
            then
              let msg =
                let uu____6512 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s" uu____6512  in
              FStar_Util.measure_execution_time msg
                (fun uu____6522  -> extract' g m)
            else extract' g m  in
          (let uu____6526 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____6526);
          res))
  