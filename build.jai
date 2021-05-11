#import "Basic";
#import "Compiler";

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
  target_options.array_bounds_check = .OFF;

  // LLVM options.
  target_options.backend = .LLVM;
  target_options.llvm_options.code_gen_optimization_level = 2; // same as saying clang -O2

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

#run build_release();

