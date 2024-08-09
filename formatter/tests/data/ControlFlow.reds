
func Test() {
  if true
    && false
    && true
    && false
    && true
    && false {
  } else if false {
    FTLog("a");
  } else {
    FTLog("b");
  }

  if true {
    FTLog("c");
  }

  while true
    && false
    && true
    && false
    && true
    && false {
    FTLog("d");
  }

  while false {
    FTLog("e");
  }

  for x in [
    "lorem",
    "ipsum",
    "dolor",
    "sit",
    "amet",
    "consectetur",
    "adipiscing",
    "elit",
    "sed",
    "do",
    "eiusmod",
    "tempor",
    "incididunt",
    "ut",
    "labore",
    "et",
    "dolore",
    "magna",
    "aliqua"
  ] {
    FTLog(x);
  }

  switch 1 {
    case 0:
      FTLog("f");
    case 1:
      FTLog("g");
    default:
      FTLog("h");
  }

  for y in [1, 2, 3] {
    FTLog(s"f: \(y)");
  }

  let f1 = (a) -> a;
  let f2 = (a) -> {
    return a;
  };
}
