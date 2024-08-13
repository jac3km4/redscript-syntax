module Test.Module

import Dummy.*

private native class NativeClass extends IScriptable {
  let a: Int32 = 0;
  let b: Int64;

  private native func NativeMethod(opt arg: Int16) -> Uint16;

  private native func NativeMethodTwo();

  final func ScriptedMethod(out arg: Int32) {
    arg = 0;
  }
}

public class ScriptedClass {
  let field: String = "Hello, World!";

  public static func New() -> ref<ScriptedClass> {
    return new ScriptedClass();
  }

  func ScriptedMethod() -> Int32 {
    return 1;
  }

  func InlineMethod() -> Int32 = 2;
}

public class GenericClass<+A extends ScriptedClass> {
  public func GenericMethod<B>() {
  }
}

struct Struct {
  let a: Int32;
  let b: Int64;
}

func LongFunc1(
  a: Int32,
  very: Int64,
  large: Uint32,
  number: Uint64,
  of: Float,
  parameters: String
) {
  LongFunc2(
    0,
    1l,
    2u,
    3ul,
    4.0,
    "lorem ipsum dolor sit amet consectetur adipiscing elit sed do eiusmod tempor incididunt ut labore"
  );

  LongFunc2(
    LongFunc2(
      0,
      1l,
      2u,
      3ul,
      4.0,
      "lorem ipsum dolor sit amet consectetur adipiscing elit sed do eiusmod tempor incididunt ut labore"
    ),
    1l,
    2u,
    3ul,
    4.0,
    "lorem"
  );
}

func LongFunc2(
  a: Int32,
  very: Int64,
  large: Uint32,
  number: Uint64,
  of: Float,
  parameters: String
) -> Int32 {
  return a;
}
