#import "Basic";
#import "File";
#import "String";

SAT_VAR :: enum s8 { UNASSIGNED :: TRUE|FALSE; FALSE :: 1; TRUE :: 2; }

Clause :: [..] int;

parse_sat_file :: (file_name: string)-> [..] SAT_VAR, [..]Clause {
  text := read_entire_file(file_name);
  lines := split(text, "\n");
  sat_vars: [..] SAT_VAR;
  clauses : [..]Clause;

  for line : lines {
    tokens := split(line, " ");
    if tokens.count == 0 {
      continue;
    }
    if equal(tokens[0], "c") {
      continue;
    }

    else if equal(tokens[0], "p") {
      num_variables := string_to_int(tokens[2]);
      num_clauses   := string_to_int(tokens[3]);
      array_reserve(*sat_vars, num_variables);
      array_reserve(*clauses, num_clauses);

      for i: 0..num_variables-1 {
        array_add(*sat_vars, SAT_VAR.UNASSIGNED);
      }

    } else {
      clause : Clause;

      for token : tokens {
        val := string_to_int(token);
        if val == 0
          break;
        array_add(*clause, val);
      }

      array_add(*clauses, clause);
    }
  }
  return sat_vars, clauses;
}

naive_sat_solver :: (vars: [..]SAT_VAR, clauses: [..]Clause, level:=0)->bool {

  is_satisfiable :: (vars: [..]SAT_VAR, clauses: [..]Clause)->bool {
    for clause : clauses {
      cl := SAT_VAR.FALSE;
      for var : clause{
        bool_value : SAT_VAR = ---;
        if var < 0 {
          var = -var;
          bool_value = vars[var-1] ^ SAT_VAR.TRUE;
        } else {
          bool_value = vars[var-1];
        }

        cl = cl | bool_value;
      }
      if cl == SAT_VAR.FALSE {
        return false;
      }
    }
    return true;
  }


  if level >= vars.count then {
    return is_satisfiable(vars, clauses);
  }
  
  vars[level] = SAT_VAR.TRUE;
  if naive_sat_solver(vars, clauses, level + 1) {
    return true;
  }

  vars[level] = SAT_VAR.FALSE;
  if naive_sat_solver(vars, clauses, level + 1) {
    return true;
  }

  vars[level] = SAT_VAR.UNASSIGNED;
  return false;
}

boolean_constant_propagation :: (f: [..]Clause, a: [..]SAT_VAR)->bool {
  TF := true;

  while(TF) {
    TF = false;
    // unit propagation
    for clause : f {
      count := 0;
      index := -1;
      is_not_total : bool = ---;
      for var_num : clause {
        is_not := var_num < 0;
        if is_not {
          var_num = (-var_num)-1;
        } else {
          var_num = var_num-1;
        }
        if a[var_num] == SAT_VAR.UNASSIGNED {
          if count < 1 {
            count = count + 1;
            index = var_num;
            is_not_total = is_not;
          } else {
            count = count + 1;
            index = -1;
            break;
          }
        } else if (a[var_num] == SAT_VAR.TRUE && !is_not) || (a[var_num]==SAT_VAR.FALSE && is_not) {
          count = 0;
          index = -1;
          break;
        }
      }

      // exactly one unassigned variable
      if count == 1 {
        if is_not_total {
          a[index] = SAT_VAR.FALSE;
        } else {
          a[index] = SAT_VAR.TRUE;
        }
        TF = true;
      }
    }

    //pure literal propagation.
    for var : a {
      if var != SAT_VAR.UNASSIGNED continue;
      val := it_index;
      pure : SAT_VAR = cast(SAT_VAR) 0;

      for clause : f {

        for var_num : clause {
          if var_num < 0 {
            var_num = -var_num - 1;
            if a[var_num] == SAT_VAR.FALSE
              continue clause;

          } else {
            var_num = var_num - 1;
            if a[var_num] == SAT_VAR.TRUE
              continue clause;
          }
        }

        for var_num : clause {
          index := var_num;
          is_not := index < 0;
          if is_not {
            index = -index - 1;
          } else {
            index = index - 1;
          }

          if val != index continue;

          if is_not {
            pure |= SAT_VAR.FALSE;
          } else {
            pure |= SAT_VAR.TRUE;
          }
        }
      }

      if pure == SAT_VAR.TRUE {
        a[val] = SAT_VAR.TRUE;
        TF = true;
      } else if pure == SAT_VAR.FALSE {
        a[val] = SAT_VAR.FALSE;
        TF = true;
      }

    }

  }

  return true;
}

conflict_drive_clause_learning :: (a: [..]SAT_VAR, f: [..]Clause)->bool {
  
  if boolean_constant_propagation(f, a) {
    return is_satisfiable(a, f);
  }

  level := 0;
  while has_unassigned_variables(a) {
    level = level + 1;
    decide(f, a);    
    while boolean_constant_propagation(f, a) {
      b, c := analyze_conflict();
      array_add(*f, c);
      if b < 0 {
        return false;
      } else {
        backtrack(f, a, b);
        level = b;
      }
    }
  }

  return true;


  // helper functions.
  backtrack :: (f: [..]Clause, a: [..]SAT_VAR, b: int) {

  }

  analyze_conflict :: ()->(int, Clause) {
    c : Clause;
    return -1, c;
  }

  decide :: (f: [..]Clause, a: [..]SAT_VAR) {

  }

  has_unassigned_variables :: (a: [..]SAT_VAR)->bool #expand {
    for var : a
      if var == SAT_VAR.UNASSIGNED return true;
    return false;
  }


  // TODO: just temporary. this is just useless
  is_satisfiable :: (vars: [..]SAT_VAR, clauses: [..]Clause)->bool {
    for clause : clauses {
      cl := SAT_VAR.FALSE;
      for var : clause{
        is_not := var < 0;
        if is_not {
          var = -var - 1;
        } else {
          var = var - 1;
        }

        bool_value : SAT_VAR = SAT_VAR.FALSE;
        if is_not && vars[var]==SAT_VAR.FALSE {
          bool_value = SAT_VAR.TRUE;
        } else if !is_not && vars[var]==SAT_VAR.TRUE {
          bool_value = SAT_VAR.TRUE;
        }
 
        if bool_value == SAT_VAR.TRUE {
          cl = SAT_VAR.TRUE;
          break;
        }
      }
      if cl == SAT_VAR.FALSE {
        return false;
      }
    }
    return true;
  }

}

main :: () {
  args := get_command_line_arguments();
  if args.count == 1 {
    print("Please supply a *.cnf sat file to the program.\n");
    return;
  }

  // parse the sat file
  file_name := args[1];
  sat_vars, clauses := parse_sat_file(file_name);
  // sat solver
  sat := conflict_drive_clause_learning(sat_vars, clauses);

  if sat {
    for var : sat_vars {
      if var == SAT_VAR.TRUE
        print(" x%    ", it_index+1);
      else
        print("-x%   ", it_index+1);
    }
    print("\nsat\n");
  } else {
    for var : sat_vars {
      if var == SAT_VAR.TRUE
        print(" x%   ", it_index+1);
      else
        print("-x%  ", it_index+1);
    }
    print("unsat\n");
  }

}






