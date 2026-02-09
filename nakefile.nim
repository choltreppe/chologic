import nake

proc build(isRelease: bool) =

  direShell "sassc src/style.sass out/style.css"

  var cc = "nim js"
  if isRelease: cc &= " -d:release -d:danger"
  direShell cc, "-o:out/app.js", "src/main.nim"
  if isRelease:
    withDir "out":
      direShell "closure-compiler --js app.js --js_output_file app.min.js --assume_function_wrapper"
      moveFile "app.min.js", "app.js"

task defaultTask, "build debug version":
  build(isRelease=false)

task "release", "build release version":
  build(isRelease=true)