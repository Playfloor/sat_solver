#import "Basic";
#import "Compiler";
#import "Process";

#run {
  option : enum {
    debug;
    release;
    test;
  } = .debug;

  args := compiler_get_command_line_arguments();
  for arg: args {
    if arg == {
    case "debug";
      option = .debug;
    case "release";
      option = .release;
    case "test";
      option = .test;
    case;
      print("Invalid commandline argument: %\n", arg);
    }
  }

  if option == {
  case .debug;
    build_debug();
  case .release;
    build_release();
  case .test;
    test_sat_solver();
  }
}

build_debug :: () {
  w := compiler_create_workspace();
  if !w {
    print("Workspace creation failed.\n");
    return;
  }
  target_options := get_build_options(w);
  target_options.output_executable_name = "sat";
  target_options.optimization_level = .DEBUG;
  target_options.backend = .X64;
  set_build_options(target_options, w);

  compiler_begin_intercept(w);
  // add all the files
  add_build_file(tprint("%/main.jai", #filepath), w);  
  while true {
    message := compiler_wait_for_message();
    if !message break;
    if message.kind == {
    case .COMPLETE;
      break;
    }
  }
  compiler_end_intercept(w);
  options := get_build_options();
  options.output_type = .NO_OUTPUT;  // No executable for the primary workspace.
  set_build_options(options);
}

build_release :: () {
  w := compiler_create_workspace();
  if !w {
    print("Workspace creation failed.\n");
    return;
  }
  target_options := get_build_options(w);
  target_options.output_executable_name = "sat";
  target_options.optimization_level = .RELEASE;
  set_optimization_level(*target_options, 2, 0);

  set_build_options(target_options, w);

  compiler_begin_intercept(w);
  // add all the files
  add_build_file(tprint("%/main.jai", #filepath), w);  
  while true {
    message := compiler_wait_for_message();
    if !message break;
    if message.kind == {
    case .COMPLETE;
      break;
    }
  }
  compiler_end_intercept(w);
  options := get_build_options();
  options.output_type = .NO_OUTPUT;  // No executable for the primary workspace.
  set_build_options(options);
}

test_sat_solver :: () {
  options := get_build_options();
  options.output_type = .NO_OUTPUT;
  set_build_options(options);

  num_passed := 0;
  num_tests := 0;

  print("Testing trivial problems...\n");
  test("1sat.cnf", 0);
  test("1unsat.cnf", 1);
  test("2sat.cnf", 0);
  test("2unsat.cnf", 1);
  test("3sat.cnf", 0);
  test("3unsat.cnf", 1);
  test("4sat.cnf", 0);
  test("4unsat.cnf", 1);
  test("5sat.cnf", 0);
  test("5unsat.cnf", 1);
  test("6sat.cnf", 0);
  test("7sat.cnf", 0);
  test("8sat.cnf", 0);

  print("Testing unsat pret problems...\n");
  test("pret60_25.cnf", 1);
  test("pret60_40.cnf", 1);
  test("pret60_60.cnf", 1);
  test("pret60_75.cnf", 1);
  test("pret150_25.cnf", 1);
  test("pret150_40.cnf", 1);
  test("pret150_60.cnf", 1);
  test("pret150_75.cnf", 1);

  print("Testing sw100 problems...\n");
  test("sw100-1.cnf", 0);
  test("sw100-2.cnf", 0);
  test("sw100-3.cnf", 0);
  test("sw100-4.cnf", 0);

  print("Testing uf-20 problems...\n");
  test("uf20-01.cnf", 0);
  test("uf20-02.cnf", 0);
  test("uf20-03.cnf", 0);
  test("uf20-04.cnf", 0);

  print("% out of % tests passed\n", num_passed, num_tests);

  test :: (file_name: string, code: int) #expand {
    num_tests += 1;
    print("Running tests/%...\n", file_name);
    print("----------------------------------------------\n");
    success, exit_code := os_run_command(tprint("%/%", #filepath, "sat"), tprint("tests/%", file_name));
    if exit_code == code {
      num_passed += 1;
      print("test % successful\n", file_name);
    } else {
      print("test % fail\n", file_name);
      `return;
    }
  }
}

