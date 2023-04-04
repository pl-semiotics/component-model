
  type val_int_size = VI_8 | VI_16 | VI_32 | VI_64
  type val_float_size = VF_32 | VF_64
  type record_field = record_field' Source.phrase
  and record_field' =
    {
      rf_name : name;
      rf_type : val_type;
    }
  and variant_case = variant_case' Source.phrase
  and variant_case' =
    {
      vc_name : name;
      vc_type : val_type;
      vc_default : name option;
    }
  and val_type = val_type' Source.phrase
  and val_type' =
    | Record of record_field list
    | Variant of variant_case list
    | List of val_type
    | Tuple of val_type list
    | Flags of name list
    | Enum of name list
    | Union of val_type list
    | Option of val_type
    | Expected of val_type * val_type
    | Unit | Bool
    | Signed of val_int_size | Unsigned of val_int_size
    | Float of val_float_size
    | Char | String
  type param = param' Source.phrase
  and param' =
    {
      p_name : name option;
      p_type : val_type;
    }
  type func_type = func_type' Source.phrase
  and func_type' =
    {
      ft_params : param list;
      ft_result : val_type;
    }
  type type_bound = type_bound' Source.phrase
  and type_bound' =
    | Bound_eq of def_type
  type type_type = type_type' Source.phrase
  and type_type' =
    | Bounded_type of type_bound
  and component_type = component_type' Source.phrase
  and component_type' = component_decl list
  and instance_type = instance_type' Source.phrase
  and instance_type' = instance_decl list
  and component_decl = component_decl' Source.phrase
  and component_decl' =
    | Component_import of import
    | Component_instance of instance_decl
  and instance_decl = instance_decl' Source.phrase
  and instance_decl' =
    | Instance_type of def_type
    | Instance_alias of alias
    | Instance_export of exportdecl
  and importdecl = importdecl' Source.phrase
  and importdecl' = { i_name : name; i_type : externtype }
  and exportdecl = exportdecl' Source.phrase
  and exportdecl' = { e_name : name; e_type : externtype }
  and externtype = externtype' Source.phrase
  and externtype' =
    | Extern_core_mod of core_moduletype
    | Extern_nonval_type of nonval_type
    | Extern_val_type of val_type
  and nonval_type = nonval_type' Source.phrase
  and nonval_type' =
    | Deftype_func of func_type
    | Deftype_type of type_type
    | Deftype_comp of component_type
    | Deftype_inst of instance_type
  and def_type = def_type' Source.phrase
  and def_type' =
    | Deftype_val of val_type
    | Deftype_nonval of nonval_type
