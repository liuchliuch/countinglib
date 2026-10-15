import Paper2.Certificates.Q6CoverageCompact.Layer12Part004

namespace Paper2.Certificates.Q6.Coverage

def stree12LLRLRLL (i : Nat) : State := if i < 9 then stree12LLRLRLLL i else stree12LLRLRLLR (i - 9)

def stree12LLRLRLRLL (i : Nat) : State := match i with | 0 => state12_392 | 1 => state12_393 | 2 => state12_394 | _ => state12_395

def stree12LLRLRLRLR (i : Nat) : State := match i with | 0 => state12_396 | 1 => state12_397 | 2 => state12_398 | 3 => state12_399 | _ => state12_400

def stree12LLRLRLRL (i : Nat) : State := if i < 4 then stree12LLRLRLRLL i else stree12LLRLRLRLR (i - 4)

def stree12LLRLRLRRL (i : Nat) : State := match i with | 0 => state12_401 | 1 => state12_402 | 2 => state12_403 | 3 => state12_404 | _ => state12_405

def stree12LLRLRLRRR (i : Nat) : State := match i with | 0 => state12_406 | 1 => state12_407 | 2 => state12_408 | 3 => state12_409 | _ => state12_410

def stree12LLRLRLRR (i : Nat) : State := if i < 5 then stree12LLRLRLRRL i else stree12LLRLRLRRR (i - 5)

def stree12LLRLRLR (i : Nat) : State := if i < 9 then stree12LLRLRLRL i else stree12LLRLRLRR (i - 9)

def stree12LLRLRL (i : Nat) : State := if i < 18 then stree12LLRLRLL i else stree12LLRLRLR (i - 18)

def stree12LLRLRRLLL (i : Nat) : State := match i with | 0 => state12_411 | 1 => state12_412 | 2 => state12_413 | _ => state12_414

def stree12LLRLRRLLR (i : Nat) : State := match i with | 0 => state12_415 | 1 => state12_416 | 2 => state12_417 | 3 => state12_418 | _ => state12_419

def stree12LLRLRRLL (i : Nat) : State := if i < 4 then stree12LLRLRRLLL i else stree12LLRLRRLLR (i - 4)

def stree12LLRLRRLRL (i : Nat) : State := match i with | 0 => state12_420 | 1 => state12_421 | 2 => state12_422 | 3 => state12_423 | _ => state12_424

def stree12LLRLRRLRR (i : Nat) : State := match i with | 0 => state12_425 | 1 => state12_426 | 2 => state12_427 | 3 => state12_428 | _ => state12_429

def stree12LLRLRRLR (i : Nat) : State := if i < 5 then stree12LLRLRRLRL i else stree12LLRLRRLRR (i - 5)

def stree12LLRLRRL (i : Nat) : State := if i < 9 then stree12LLRLRRLL i else stree12LLRLRRLR (i - 9)

def stree12LLRLRRRLL (i : Nat) : State := match i with | 0 => state12_430 | 1 => state12_431 | 2 => state12_432 | _ => state12_433

def stree12LLRLRRRLR (i : Nat) : State := match i with | 0 => state12_434 | 1 => state12_435 | 2 => state12_436 | 3 => state12_437 | _ => state12_438

def stree12LLRLRRRL (i : Nat) : State := if i < 4 then stree12LLRLRRRLL i else stree12LLRLRRRLR (i - 4)

def stree12LLRLRRRRL (i : Nat) : State := match i with | 0 => state12_439 | 1 => state12_440 | 2 => state12_441 | 3 => state12_442 | _ => state12_443

def stree12LLRLRRRRR (i : Nat) : State := match i with | 0 => state12_444 | 1 => state12_445 | 2 => state12_446 | 3 => state12_447 | _ => state12_448

def stree12LLRLRRRR (i : Nat) : State := if i < 5 then stree12LLRLRRRRL i else stree12LLRLRRRRR (i - 5)

def stree12LLRLRRR (i : Nat) : State := if i < 9 then stree12LLRLRRRL i else stree12LLRLRRRR (i - 9)

def stree12LLRLRR (i : Nat) : State := if i < 19 then stree12LLRLRRL i else stree12LLRLRRR (i - 19)

def stree12LLRLR (i : Nat) : State := if i < 37 then stree12LLRLRL i else stree12LLRLRR (i - 37)

def stree12LLRL (i : Nat) : State := if i < 75 then stree12LLRLL i else stree12LLRLR (i - 75)

def stree12LLRRLLLLL (i : Nat) : State := match i with | 0 => state12_449 | 1 => state12_450 | 2 => state12_451 | _ => state12_452

def stree12LLRRLLLLR (i : Nat) : State := match i with | 0 => state12_453 | 1 => state12_454 | 2 => state12_455 | 3 => state12_456 | _ => state12_457

def stree12LLRRLLLL (i : Nat) : State := if i < 4 then stree12LLRRLLLLL i else stree12LLRRLLLLR (i - 4)

def stree12LLRRLLLRL (i : Nat) : State := match i with | 0 => state12_458 | 1 => state12_459 | 2 => state12_460 | _ => state12_461

def stree12LLRRLLLRR (i : Nat) : State := match i with | 0 => state12_462 | 1 => state12_463 | 2 => state12_464 | 3 => state12_465 | _ => state12_466

def stree12LLRRLLLR (i : Nat) : State := if i < 4 then stree12LLRRLLLRL i else stree12LLRRLLLRR (i - 4)

def stree12LLRRLLL (i : Nat) : State := if i < 9 then stree12LLRRLLLL i else stree12LLRRLLLR (i - 9)

def stree12LLRRLLRLL (i : Nat) : State := match i with | 0 => state12_467 | 1 => state12_468 | 2 => state12_469 | _ => state12_470

def stree12LLRRLLRLR (i : Nat) : State := match i with | 0 => state12_471 | 1 => state12_472 | 2 => state12_473 | 3 => state12_474 | _ => state12_475

def stree12LLRRLLRL (i : Nat) : State := if i < 4 then stree12LLRRLLRLL i else stree12LLRRLLRLR (i - 4)

def stree12LLRRLLRRL (i : Nat) : State := match i with | 0 => state12_476 | 1 => state12_477 | 2 => state12_478 | 3 => state12_479 | _ => state12_480

def stree12LLRRLLRRR (i : Nat) : State := match i with | 0 => state12_481 | 1 => state12_482 | 2 => state12_483 | 3 => state12_484 | _ => state12_485

def stree12LLRRLLRR (i : Nat) : State := if i < 5 then stree12LLRRLLRRL i else stree12LLRRLLRRR (i - 5)

def stree12LLRRLLR (i : Nat) : State := if i < 9 then stree12LLRRLLRL i else stree12LLRRLLRR (i - 9)

def stree12LLRRLL (i : Nat) : State := if i < 18 then stree12LLRRLLL i else stree12LLRRLLR (i - 18)

def stree12LLRRLRLLL (i : Nat) : State := match i with | 0 => state12_486 | 1 => state12_487 | 2 => state12_488 | _ => state12_489

def stree12LLRRLRLLR (i : Nat) : State := match i with | 0 => state12_490 | 1 => state12_491 | 2 => state12_492 | 3 => state12_493 | _ => state12_494

def stree12LLRRLRLL (i : Nat) : State := if i < 4 then stree12LLRRLRLLL i else stree12LLRRLRLLR (i - 4)

def stree12LLRRLRLRL (i : Nat) : State := match i with | 0 => state12_495 | 1 => state12_496 | 2 => state12_497 | 3 => state12_498 | _ => state12_499

def stree12LLRRLRLRR (i : Nat) : State := match i with | 0 => state12_500 | 1 => state12_501 | 2 => state12_502 | 3 => state12_503 | _ => state12_504

def stree12LLRRLRLR (i : Nat) : State := if i < 5 then stree12LLRRLRLRL i else stree12LLRRLRLRR (i - 5)

def stree12LLRRLRL (i : Nat) : State := if i < 9 then stree12LLRRLRLL i else stree12LLRRLRLR (i - 9)

def stree12LLRRLRRLL (i : Nat) : State := match i with | 0 => state12_505 | 1 => state12_506 | 2 => state12_507 | _ => state12_508

def stree12LLRRLRRLR (i : Nat) : State := match i with | 0 => state12_509 | 1 => state12_510 | 2 => state12_511 | 3 => state12_512 | _ => state12_513

def stree12LLRRLRRL (i : Nat) : State := if i < 4 then stree12LLRRLRRLL i else stree12LLRRLRRLR (i - 4)

def stree12LLRRLRRRL (i : Nat) : State := match i with | 0 => state12_514 | 1 => state12_515 | 2 => state12_516 | 3 => state12_517 | _ => state12_518

def stree12LLRRLRRRR (i : Nat) : State := match i with | 0 => state12_519 | 1 => state12_520 | 2 => state12_521 | 3 => state12_522 | _ => state12_523

def stree12LLRRLRRR (i : Nat) : State := if i < 5 then stree12LLRRLRRRL i else stree12LLRRLRRRR (i - 5)

def stree12LLRRLRR (i : Nat) : State := if i < 9 then stree12LLRRLRRL i else stree12LLRRLRRR (i - 9)

def stree12LLRRLR (i : Nat) : State := if i < 19 then stree12LLRRLRL i else stree12LLRRLRR (i - 19)

def stree12LLRRL (i : Nat) : State := if i < 37 then stree12LLRRLL i else stree12LLRRLR (i - 37)

def stree12LLRRRLLLL (i : Nat) : State := match i with | 0 => state12_524 | 1 => state12_525 | 2 => state12_526 | _ => state12_527

def stree12LLRRRLLLR (i : Nat) : State := match i with | 0 => state12_528 | 1 => state12_529 | 2 => state12_530 | 3 => state12_531 | _ => state12_532

def stree12LLRRRLLL (i : Nat) : State := if i < 4 then stree12LLRRRLLLL i else stree12LLRRRLLLR (i - 4)

def stree12LLRRRLLRL (i : Nat) : State := match i with | 0 => state12_533 | 1 => state12_534 | 2 => state12_535 | _ => state12_536

def stree12LLRRRLLRR (i : Nat) : State := match i with | 0 => state12_537 | 1 => state12_538 | 2 => state12_539 | 3 => state12_540 | _ => state12_541

def stree12LLRRRLLR (i : Nat) : State := if i < 4 then stree12LLRRRLLRL i else stree12LLRRRLLRR (i - 4)

def stree12LLRRRLL (i : Nat) : State := if i < 9 then stree12LLRRRLLL i else stree12LLRRRLLR (i - 9)

def stree12LLRRRLRLL (i : Nat) : State := match i with | 0 => state12_542 | 1 => state12_543 | 2 => state12_544 | _ => state12_545

def stree12LLRRRLRLR (i : Nat) : State := match i with | 0 => state12_546 | 1 => state12_547 | 2 => state12_548 | 3 => state12_549 | _ => state12_550

def stree12LLRRRLRL (i : Nat) : State := if i < 4 then stree12LLRRRLRLL i else stree12LLRRRLRLR (i - 4)

def stree12LLRRRLRRL (i : Nat) : State := match i with | 0 => state12_551 | 1 => state12_552 | 2 => state12_553 | 3 => state12_554 | _ => state12_555

def stree12LLRRRLRRR (i : Nat) : State := match i with | 0 => state12_556 | 1 => state12_557 | 2 => state12_558 | 3 => state12_559 | _ => state12_560

def stree12LLRRRLRR (i : Nat) : State := if i < 5 then stree12LLRRRLRRL i else stree12LLRRRLRRR (i - 5)

def stree12LLRRRLR (i : Nat) : State := if i < 9 then stree12LLRRRLRL i else stree12LLRRRLRR (i - 9)

def stree12LLRRRL (i : Nat) : State := if i < 18 then stree12LLRRRLL i else stree12LLRRRLR (i - 18)

def stree12LLRRRRLLL (i : Nat) : State := match i with | 0 => state12_561 | 1 => state12_562 | 2 => state12_563 | _ => state12_564

def stree12LLRRRRLLR (i : Nat) : State := match i with | 0 => state12_565 | 1 => state12_566 | 2 => state12_567 | 3 => state12_568 | _ => state12_569

def stree12LLRRRRLL (i : Nat) : State := if i < 4 then stree12LLRRRRLLL i else stree12LLRRRRLLR (i - 4)

def stree12LLRRRRLRL (i : Nat) : State := match i with | 0 => state12_570 | 1 => state12_571 | 2 => state12_572 | 3 => state12_573 | _ => state12_574

def stree12LLRRRRLRR (i : Nat) : State := match i with | 0 => state12_575 | 1 => state12_576 | 2 => state12_577 | 3 => state12_578 | _ => state12_579

def stree12LLRRRRLR (i : Nat) : State := if i < 5 then stree12LLRRRRLRL i else stree12LLRRRRLRR (i - 5)

def stree12LLRRRRL (i : Nat) : State := if i < 9 then stree12LLRRRRLL i else stree12LLRRRRLR (i - 9)

def stree12LLRRRRRLL (i : Nat) : State := match i with | 0 => state12_580 | 1 => state12_581 | 2 => state12_582 | _ => state12_583

def stree12LLRRRRRLR (i : Nat) : State := match i with | 0 => state12_584 | 1 => state12_585 | 2 => state12_586 | 3 => state12_587 | _ => state12_588

def stree12LLRRRRRL (i : Nat) : State := if i < 4 then stree12LLRRRRRLL i else stree12LLRRRRRLR (i - 4)

def stree12LLRRRRRRL (i : Nat) : State := match i with | 0 => state12_589 | 1 => state12_590 | 2 => state12_591 | 3 => state12_592 | _ => state12_593

def stree12LLRRRRRRR (i : Nat) : State := match i with | 0 => state12_594 | 1 => state12_595 | 2 => state12_596 | 3 => state12_597 | _ => state12_598

def stree12LLRRRRRR (i : Nat) : State := if i < 5 then stree12LLRRRRRRL i else stree12LLRRRRRRR (i - 5)

def stree12LLRRRRR (i : Nat) : State := if i < 9 then stree12LLRRRRRL i else stree12LLRRRRRR (i - 9)

def stree12LLRRRR (i : Nat) : State := if i < 19 then stree12LLRRRRL i else stree12LLRRRRR (i - 19)

def stree12LLRRR (i : Nat) : State := if i < 37 then stree12LLRRRL i else stree12LLRRRR (i - 37)

def stree12LLRR (i : Nat) : State := if i < 75 then stree12LLRRL i else stree12LLRRR (i - 75)

def stree12LLR (i : Nat) : State := if i < 150 then stree12LLRL i else stree12LLRR (i - 150)

def stree12LL (i : Nat) : State := if i < 299 then stree12LLL i else stree12LLR (i - 299)

def stree12LRLLLLLLL (i : Nat) : State := match i with | 0 => state12_599 | 1 => state12_600 | 2 => state12_601 | _ => state12_602

def stree12LRLLLLLLR (i : Nat) : State := match i with | 0 => state12_603 | 1 => state12_604 | 2 => state12_605 | 3 => state12_606 | _ => state12_607

def stree12LRLLLLLL (i : Nat) : State := if i < 4 then stree12LRLLLLLLL i else stree12LRLLLLLLR (i - 4)

def stree12LRLLLLLRL (i : Nat) : State := match i with | 0 => state12_608 | 1 => state12_609 | 2 => state12_610 | _ => state12_611

def stree12LRLLLLLRR (i : Nat) : State := match i with | 0 => state12_612 | 1 => state12_613 | 2 => state12_614 | 3 => state12_615 | _ => state12_616

def stree12LRLLLLLR (i : Nat) : State := if i < 4 then stree12LRLLLLLRL i else stree12LRLLLLLRR (i - 4)

def stree12LRLLLLL (i : Nat) : State := if i < 9 then stree12LRLLLLLL i else stree12LRLLLLLR (i - 9)

def stree12LRLLLLRLL (i : Nat) : State := match i with | 0 => state12_617 | 1 => state12_618 | 2 => state12_619 | _ => state12_620

def stree12LRLLLLRLR (i : Nat) : State := match i with | 0 => state12_621 | 1 => state12_622 | 2 => state12_623 | 3 => state12_624 | _ => state12_625

def stree12LRLLLLRL (i : Nat) : State := if i < 4 then stree12LRLLLLRLL i else stree12LRLLLLRLR (i - 4)

def stree12LRLLLLRRL (i : Nat) : State := match i with | 0 => state12_626 | 1 => state12_627 | 2 => state12_628 | 3 => state12_629 | _ => state12_630

def stree12LRLLLLRRR (i : Nat) : State := match i with | 0 => state12_631 | 1 => state12_632 | 2 => state12_633 | 3 => state12_634 | _ => state12_635

def stree12LRLLLLRR (i : Nat) : State := if i < 5 then stree12LRLLLLRRL i else stree12LRLLLLRRR (i - 5)

def stree12LRLLLLR (i : Nat) : State := if i < 9 then stree12LRLLLLRL i else stree12LRLLLLRR (i - 9)

def stree12LRLLLL (i : Nat) : State := if i < 18 then stree12LRLLLLL i else stree12LRLLLLR (i - 18)

def stree12LRLLLRLLL (i : Nat) : State := match i with | 0 => state12_636 | 1 => state12_637 | 2 => state12_638 | _ => state12_639

def stree12LRLLLRLLR (i : Nat) : State := match i with | 0 => state12_640 | 1 => state12_641 | 2 => state12_642 | 3 => state12_643 | _ => state12_644

def stree12LRLLLRLL (i : Nat) : State := if i < 4 then stree12LRLLLRLLL i else stree12LRLLLRLLR (i - 4)

def stree12LRLLLRLRL (i : Nat) : State := match i with | 0 => state12_645 | 1 => state12_646 | 2 => state12_647 | _ => state12_648

def stree12LRLLLRLRR (i : Nat) : State := match i with | 0 => state12_649 | 1 => state12_650 | 2 => state12_651 | 3 => state12_652 | _ => state12_653

def stree12LRLLLRLR (i : Nat) : State := if i < 4 then stree12LRLLLRLRL i else stree12LRLLLRLRR (i - 4)

def stree12LRLLLRL (i : Nat) : State := if i < 9 then stree12LRLLLRLL i else stree12LRLLLRLR (i - 9)

def stree12LRLLLRRLL (i : Nat) : State := match i with | 0 => state12_654 | 1 => state12_655 | 2 => state12_656 | _ => state12_657

def stree12LRLLLRRLR (i : Nat) : State := match i with | 0 => state12_658 | 1 => state12_659 | 2 => state12_660 | 3 => state12_661 | _ => state12_662

def stree12LRLLLRRL (i : Nat) : State := if i < 4 then stree12LRLLLRRLL i else stree12LRLLLRRLR (i - 4)

def stree12LRLLLRRRL (i : Nat) : State := match i with | 0 => state12_663 | 1 => state12_664 | 2 => state12_665 | 3 => state12_666 | _ => state12_667

def stree12LRLLLRRRR (i : Nat) : State := match i with | 0 => state12_668 | 1 => state12_669 | 2 => state12_670 | 3 => state12_671 | _ => state12_672

def stree12LRLLLRRR (i : Nat) : State := if i < 5 then stree12LRLLLRRRL i else stree12LRLLLRRRR (i - 5)

def stree12LRLLLRR (i : Nat) : State := if i < 9 then stree12LRLLLRRL i else stree12LRLLLRRR (i - 9)

def stree12LRLLLR (i : Nat) : State := if i < 18 then stree12LRLLLRL i else stree12LRLLLRR (i - 18)

def stree12LRLLL (i : Nat) : State := if i < 37 then stree12LRLLLL i else stree12LRLLLR (i - 37)

def stree12LRLLRLLLL (i : Nat) : State := match i with | 0 => state12_673 | 1 => state12_674 | 2 => state12_675 | _ => state12_676

def stree12LRLLRLLLR (i : Nat) : State := match i with | 0 => state12_677 | 1 => state12_678 | 2 => state12_679 | 3 => state12_680 | _ => state12_681

def stree12LRLLRLLL (i : Nat) : State := if i < 4 then stree12LRLLRLLLL i else stree12LRLLRLLLR (i - 4)

def stree12LRLLRLLRL (i : Nat) : State := match i with | 0 => state12_682 | 1 => state12_683 | 2 => state12_684 | _ => state12_685

def stree12LRLLRLLRR (i : Nat) : State := match i with | 0 => state12_686 | 1 => state12_687 | 2 => state12_688 | 3 => state12_689 | _ => state12_690

def stree12LRLLRLLR (i : Nat) : State := if i < 4 then stree12LRLLRLLRL i else stree12LRLLRLLRR (i - 4)

def stree12LRLLRLL (i : Nat) : State := if i < 9 then stree12LRLLRLLL i else stree12LRLLRLLR (i - 9)

def stree12LRLLRLRLL (i : Nat) : State := match i with | 0 => state12_691 | 1 => state12_692 | 2 => state12_693 | _ => state12_694

def stree12LRLLRLRLR (i : Nat) : State := match i with | 0 => state12_695 | 1 => state12_696 | 2 => state12_697 | 3 => state12_698 | _ => state12_699

def stree12LRLLRLRL (i : Nat) : State := if i < 4 then stree12LRLLRLRLL i else stree12LRLLRLRLR (i - 4)

def stree12LRLLRLRRL (i : Nat) : State := match i with | 0 => state12_700 | 1 => state12_701 | 2 => state12_702 | 3 => state12_703 | _ => state12_704

def stree12LRLLRLRRR (i : Nat) : State := match i with | 0 => state12_705 | 1 => state12_706 | 2 => state12_707 | 3 => state12_708 | _ => state12_709

def stree12LRLLRLRR (i : Nat) : State := if i < 5 then stree12LRLLRLRRL i else stree12LRLLRLRRR (i - 5)

def stree12LRLLRLR (i : Nat) : State := if i < 9 then stree12LRLLRLRL i else stree12LRLLRLRR (i - 9)

def stree12LRLLRL (i : Nat) : State := if i < 18 then stree12LRLLRLL i else stree12LRLLRLR (i - 18)

def stree12LRLLRRLLL (i : Nat) : State := match i with | 0 => state12_710 | 1 => state12_711 | 2 => state12_712 | _ => state12_713

def stree12LRLLRRLLR (i : Nat) : State := match i with | 0 => state12_714 | 1 => state12_715 | 2 => state12_716 | 3 => state12_717 | _ => state12_718

def stree12LRLLRRLL (i : Nat) : State := if i < 4 then stree12LRLLRRLLL i else stree12LRLLRRLLR (i - 4)

def stree12LRLLRRLRL (i : Nat) : State := match i with | 0 => state12_719 | 1 => state12_720 | 2 => state12_721 | 3 => state12_722 | _ => state12_723

def stree12LRLLRRLRR (i : Nat) : State := match i with | 0 => state12_724 | 1 => state12_725 | 2 => state12_726 | 3 => state12_727 | _ => state12_728

def stree12LRLLRRLR (i : Nat) : State := if i < 5 then stree12LRLLRRLRL i else stree12LRLLRRLRR (i - 5)

def stree12LRLLRRL (i : Nat) : State := if i < 9 then stree12LRLLRRLL i else stree12LRLLRRLR (i - 9)

def stree12LRLLRRRLL (i : Nat) : State := match i with | 0 => state12_729 | 1 => state12_730 | 2 => state12_731 | _ => state12_732

def stree12LRLLRRRLR (i : Nat) : State := match i with | 0 => state12_733 | 1 => state12_734 | 2 => state12_735 | 3 => state12_736 | _ => state12_737

def stree12LRLLRRRL (i : Nat) : State := if i < 4 then stree12LRLLRRRLL i else stree12LRLLRRRLR (i - 4)

def stree12LRLLRRRRL (i : Nat) : State := match i with | 0 => state12_738 | 1 => state12_739 | 2 => state12_740 | 3 => state12_741 | _ => state12_742

def stree12LRLLRRRRR (i : Nat) : State := match i with | 0 => state12_743 | 1 => state12_744 | 2 => state12_745 | 3 => state12_746 | _ => state12_747

def stree12LRLLRRRR (i : Nat) : State := if i < 5 then stree12LRLLRRRRL i else stree12LRLLRRRRR (i - 5)

def stree12LRLLRRR (i : Nat) : State := if i < 9 then stree12LRLLRRRL i else stree12LRLLRRRR (i - 9)

def stree12LRLLRR (i : Nat) : State := if i < 19 then stree12LRLLRRL i else stree12LRLLRRR (i - 19)

def stree12LRLLR (i : Nat) : State := if i < 37 then stree12LRLLRL i else stree12LRLLRR (i - 37)

def stree12LRLL (i : Nat) : State := if i < 74 then stree12LRLLL i else stree12LRLLR (i - 74)

def stree12LRLRLLLLL (i : Nat) : State := match i with | 0 => state12_748 | 1 => state12_749 | 2 => state12_750 | _ => state12_751

def stree12LRLRLLLLR (i : Nat) : State := match i with | 0 => state12_752 | 1 => state12_753 | 2 => state12_754 | 3 => state12_755 | _ => state12_756

def stree12LRLRLLLL (i : Nat) : State := if i < 4 then stree12LRLRLLLLL i else stree12LRLRLLLLR (i - 4)

def stree12LRLRLLLRL (i : Nat) : State := match i with | 0 => state12_757 | 1 => state12_758 | 2 => state12_759 | _ => state12_760

def stree12LRLRLLLRR (i : Nat) : State := match i with | 0 => state12_761 | 1 => state12_762 | 2 => state12_763 | 3 => state12_764 | _ => state12_765

def stree12LRLRLLLR (i : Nat) : State := if i < 4 then stree12LRLRLLLRL i else stree12LRLRLLLRR (i - 4)

def stree12LRLRLLL (i : Nat) : State := if i < 9 then stree12LRLRLLLL i else stree12LRLRLLLR (i - 9)

def stree12LRLRLLRLL (i : Nat) : State := match i with | 0 => state12_766 | 1 => state12_767 | 2 => state12_768 | _ => state12_769

def stree12LRLRLLRLR (i : Nat) : State := match i with | 0 => state12_770 | 1 => state12_771 | 2 => state12_772 | 3 => state12_773 | _ => state12_774

def stree12LRLRLLRL (i : Nat) : State := if i < 4 then stree12LRLRLLRLL i else stree12LRLRLLRLR (i - 4)

def stree12LRLRLLRRL (i : Nat) : State := match i with | 0 => state12_775 | 1 => state12_776 | 2 => state12_777 | 3 => state12_778 | _ => state12_779

def stree12LRLRLLRRR (i : Nat) : State := match i with | 0 => state12_780 | 1 => state12_781 | 2 => state12_782 | 3 => state12_783 | _ => state12_784

def stree12LRLRLLRR (i : Nat) : State := if i < 5 then stree12LRLRLLRRL i else stree12LRLRLLRRR (i - 5)

def stree12LRLRLLR (i : Nat) : State := if i < 9 then stree12LRLRLLRL i else stree12LRLRLLRR (i - 9)

def stree12LRLRLL (i : Nat) : State := if i < 18 then stree12LRLRLLL i else stree12LRLRLLR (i - 18)

def stree12LRLRLRLLL (i : Nat) : State := match i with | 0 => state12_785 | 1 => state12_786 | 2 => state12_787 | _ => state12_788

def stree12LRLRLRLLR (i : Nat) : State := match i with | 0 => state12_789 | 1 => state12_790 | 2 => state12_791 | 3 => state12_792 | _ => state12_793

def stree12LRLRLRLL (i : Nat) : State := if i < 4 then stree12LRLRLRLLL i else stree12LRLRLRLLR (i - 4)

def stree12LRLRLRLRL (i : Nat) : State := match i with | 0 => state12_794 | 1 => state12_795 | 2 => state12_796 | 3 => state12_797 | _ => state12_798

def stree12LRLRLRLRR (i : Nat) : State := match i with | 0 => state12_799 | 1 => state12_800 | 2 => state12_801 | 3 => state12_802 | _ => state12_803

def stree12LRLRLRLR (i : Nat) : State := if i < 5 then stree12LRLRLRLRL i else stree12LRLRLRLRR (i - 5)

def stree12LRLRLRL (i : Nat) : State := if i < 9 then stree12LRLRLRLL i else stree12LRLRLRLR (i - 9)

def stree12LRLRLRRLL (i : Nat) : State := match i with | 0 => state12_804 | 1 => state12_805 | 2 => state12_806 | _ => state12_807

def stree12LRLRLRRLR (i : Nat) : State := match i with | 0 => state12_808 | 1 => state12_809 | 2 => state12_810 | 3 => state12_811 | _ => state12_812

def stree12LRLRLRRL (i : Nat) : State := if i < 4 then stree12LRLRLRRLL i else stree12LRLRLRRLR (i - 4)

def stree12LRLRLRRRL (i : Nat) : State := match i with | 0 => state12_813 | 1 => state12_814 | 2 => state12_815 | 3 => state12_816 | _ => state12_817

def stree12LRLRLRRRR (i : Nat) : State := match i with | 0 => state12_818 | 1 => state12_819 | 2 => state12_820 | 3 => state12_821 | _ => state12_822

def stree12LRLRLRRR (i : Nat) : State := if i < 5 then stree12LRLRLRRRL i else stree12LRLRLRRRR (i - 5)

def stree12LRLRLRR (i : Nat) : State := if i < 9 then stree12LRLRLRRL i else stree12LRLRLRRR (i - 9)

def stree12LRLRLR (i : Nat) : State := if i < 19 then stree12LRLRLRL i else stree12LRLRLRR (i - 19)

def stree12LRLRL (i : Nat) : State := if i < 37 then stree12LRLRLL i else stree12LRLRLR (i - 37)

def stree12LRLRRLLLL (i : Nat) : State := match i with | 0 => state12_823 | 1 => state12_824 | 2 => state12_825 | _ => state12_826

def stree12LRLRRLLLR (i : Nat) : State := match i with | 0 => state12_827 | 1 => state12_828 | 2 => state12_829 | 3 => state12_830 | _ => state12_831

def stree12LRLRRLLL (i : Nat) : State := if i < 4 then stree12LRLRRLLLL i else stree12LRLRRLLLR (i - 4)

def stree12LRLRRLLRL (i : Nat) : State := match i with | 0 => state12_832 | 1 => state12_833 | 2 => state12_834 | _ => state12_835

def stree12LRLRRLLRR (i : Nat) : State := match i with | 0 => state12_836 | 1 => state12_837 | 2 => state12_838 | 3 => state12_839 | _ => state12_840

def stree12LRLRRLLR (i : Nat) : State := if i < 4 then stree12LRLRRLLRL i else stree12LRLRRLLRR (i - 4)

def stree12LRLRRLL (i : Nat) : State := if i < 9 then stree12LRLRRLLL i else stree12LRLRRLLR (i - 9)

def stree12LRLRRLRLL (i : Nat) : State := match i with | 0 => state12_841 | 1 => state12_842 | 2 => state12_843 | _ => state12_844

def stree12LRLRRLRLR (i : Nat) : State := match i with | 0 => state12_845 | 1 => state12_846 | 2 => state12_847 | 3 => state12_848 | _ => state12_849

def stree12LRLRRLRL (i : Nat) : State := if i < 4 then stree12LRLRRLRLL i else stree12LRLRRLRLR (i - 4)

def stree12LRLRRLRRL (i : Nat) : State := match i with | 0 => state12_850 | 1 => state12_851 | 2 => state12_852 | 3 => state12_853 | _ => state12_854

def stree12LRLRRLRRR (i : Nat) : State := match i with | 0 => state12_855 | 1 => state12_856 | 2 => state12_857 | 3 => state12_858 | _ => state12_859

def stree12LRLRRLRR (i : Nat) : State := if i < 5 then stree12LRLRRLRRL i else stree12LRLRRLRRR (i - 5)

def stree12LRLRRLR (i : Nat) : State := if i < 9 then stree12LRLRRLRL i else stree12LRLRRLRR (i - 9)

def stree12LRLRRL (i : Nat) : State := if i < 18 then stree12LRLRRLL i else stree12LRLRRLR (i - 18)

def stree12LRLRRRLLL (i : Nat) : State := match i with | 0 => state12_860 | 1 => state12_861 | 2 => state12_862 | _ => state12_863

def stree12LRLRRRLLR (i : Nat) : State := match i with | 0 => state12_864 | 1 => state12_865 | 2 => state12_866 | 3 => state12_867 | _ => state12_868

def stree12LRLRRRLL (i : Nat) : State := if i < 4 then stree12LRLRRRLLL i else stree12LRLRRRLLR (i - 4)

def stree12LRLRRRLRL (i : Nat) : State := match i with | 0 => state12_869 | 1 => state12_870 | 2 => state12_871 | 3 => state12_872 | _ => state12_873

def stree12LRLRRRLRR (i : Nat) : State := match i with | 0 => state12_874 | 1 => state12_875 | 2 => state12_876 | 3 => state12_877 | _ => state12_878

def stree12LRLRRRLR (i : Nat) : State := if i < 5 then stree12LRLRRRLRL i else stree12LRLRRRLRR (i - 5)

def stree12LRLRRRL (i : Nat) : State := if i < 9 then stree12LRLRRRLL i else stree12LRLRRRLR (i - 9)

def stree12LRLRRRRLL (i : Nat) : State := match i with | 0 => state12_879 | 1 => state12_880 | 2 => state12_881 | _ => state12_882

def stree12LRLRRRRLR (i : Nat) : State := match i with | 0 => state12_883 | 1 => state12_884 | 2 => state12_885 | 3 => state12_886 | _ => state12_887

def stree12LRLRRRRL (i : Nat) : State := if i < 4 then stree12LRLRRRRLL i else stree12LRLRRRRLR (i - 4)

def stree12LRLRRRRRL (i : Nat) : State := match i with | 0 => state12_888 | 1 => state12_889 | 2 => state12_890 | 3 => state12_891 | _ => state12_892

def stree12LRLRRRRRR (i : Nat) : State := match i with | 0 => state12_893 | 1 => state12_894 | 2 => state12_895 | 3 => state12_896 | _ => state12_897

def stree12LRLRRRRR (i : Nat) : State := if i < 5 then stree12LRLRRRRRL i else stree12LRLRRRRRR (i - 5)

def stree12LRLRRRR (i : Nat) : State := if i < 9 then stree12LRLRRRRL i else stree12LRLRRRRR (i - 9)

def stree12LRLRRR (i : Nat) : State := if i < 19 then stree12LRLRRRL i else stree12LRLRRRR (i - 19)

def stree12LRLRR (i : Nat) : State := if i < 37 then stree12LRLRRL i else stree12LRLRRR (i - 37)

def stree12LRLR (i : Nat) : State := if i < 75 then stree12LRLRL i else stree12LRLRR (i - 75)

def stree12LRL (i : Nat) : State := if i < 149 then stree12LRLL i else stree12LRLR (i - 149)

def stree12LRRLLLLLL (i : Nat) : State := match i with | 0 => state12_898 | 1 => state12_899 | 2 => state12_900 | _ => state12_901

def stree12LRRLLLLLR (i : Nat) : State := match i with | 0 => state12_902 | 1 => state12_903 | 2 => state12_904 | 3 => state12_905 | _ => state12_906

def stree12LRRLLLLL (i : Nat) : State := if i < 4 then stree12LRRLLLLLL i else stree12LRRLLLLLR (i - 4)

def stree12LRRLLLLRL (i : Nat) : State := match i with | 0 => state12_907 | 1 => state12_908 | 2 => state12_909 | _ => state12_910

def stree12LRRLLLLRR (i : Nat) : State := match i with | 0 => state12_911 | 1 => state12_912 | 2 => state12_913 | 3 => state12_914 | _ => state12_915

def stree12LRRLLLLR (i : Nat) : State := if i < 4 then stree12LRRLLLLRL i else stree12LRRLLLLRR (i - 4)

def stree12LRRLLLL (i : Nat) : State := if i < 9 then stree12LRRLLLLL i else stree12LRRLLLLR (i - 9)

def stree12LRRLLLRLL (i : Nat) : State := match i with | 0 => state12_916 | 1 => state12_917 | 2 => state12_918 | _ => state12_919

def stree12LRRLLLRLR (i : Nat) : State := match i with | 0 => state12_920 | 1 => state12_921 | 2 => state12_922 | 3 => state12_923 | _ => state12_924

def stree12LRRLLLRL (i : Nat) : State := if i < 4 then stree12LRRLLLRLL i else stree12LRRLLLRLR (i - 4)

def stree12LRRLLLRRL (i : Nat) : State := match i with | 0 => state12_925 | 1 => state12_926 | 2 => state12_927 | 3 => state12_928 | _ => state12_929

def stree12LRRLLLRRR (i : Nat) : State := match i with | 0 => state12_930 | 1 => state12_931 | 2 => state12_932 | 3 => state12_933 | _ => state12_934

def stree12LRRLLLRR (i : Nat) : State := if i < 5 then stree12LRRLLLRRL i else stree12LRRLLLRRR (i - 5)

def stree12LRRLLLR (i : Nat) : State := if i < 9 then stree12LRRLLLRL i else stree12LRRLLLRR (i - 9)

def stree12LRRLLL (i : Nat) : State := if i < 18 then stree12LRRLLLL i else stree12LRRLLLR (i - 18)

def stree12LRRLLRLLL (i : Nat) : State := match i with | 0 => state12_935 | 1 => state12_936 | 2 => state12_937 | _ => state12_938

def stree12LRRLLRLLR (i : Nat) : State := match i with | 0 => state12_939 | 1 => state12_940 | 2 => state12_941 | 3 => state12_942 | _ => state12_943

def stree12LRRLLRLL (i : Nat) : State := if i < 4 then stree12LRRLLRLLL i else stree12LRRLLRLLR (i - 4)

def stree12LRRLLRLRL (i : Nat) : State := match i with | 0 => state12_944 | 1 => state12_945 | 2 => state12_946 | 3 => state12_947 | _ => state12_948

def stree12LRRLLRLRR (i : Nat) : State := match i with | 0 => state12_949 | 1 => state12_950 | 2 => state12_951 | 3 => state12_952 | _ => state12_953

def stree12LRRLLRLR (i : Nat) : State := if i < 5 then stree12LRRLLRLRL i else stree12LRRLLRLRR (i - 5)

def stree12LRRLLRL (i : Nat) : State := if i < 9 then stree12LRRLLRLL i else stree12LRRLLRLR (i - 9)

def stree12LRRLLRRLL (i : Nat) : State := match i with | 0 => state12_954 | 1 => state12_955 | 2 => state12_956 | _ => state12_957

def stree12LRRLLRRLR (i : Nat) : State := match i with | 0 => state12_958 | 1 => state12_959 | 2 => state12_960 | 3 => state12_961 | _ => state12_962

def stree12LRRLLRRL (i : Nat) : State := if i < 4 then stree12LRRLLRRLL i else stree12LRRLLRRLR (i - 4)

def stree12LRRLLRRRL (i : Nat) : State := match i with | 0 => state12_963 | 1 => state12_964 | 2 => state12_965 | 3 => state12_966 | _ => state12_967

def stree12LRRLLRRRR (i : Nat) : State := match i with | 0 => state12_968 | 1 => state12_969 | 2 => state12_970 | 3 => state12_971 | _ => state12_972

def stree12LRRLLRRR (i : Nat) : State := if i < 5 then stree12LRRLLRRRL i else stree12LRRLLRRRR (i - 5)

def stree12LRRLLRR (i : Nat) : State := if i < 9 then stree12LRRLLRRL i else stree12LRRLLRRR (i - 9)

def stree12LRRLLR (i : Nat) : State := if i < 19 then stree12LRRLLRL i else stree12LRRLLRR (i - 19)

def stree12LRRLL (i : Nat) : State := if i < 37 then stree12LRRLLL i else stree12LRRLLR (i - 37)

def stree12LRRLRLLLL (i : Nat) : State := match i with | 0 => state12_973 | 1 => state12_974 | 2 => state12_975 | _ => state12_976

def stree12LRRLRLLLR (i : Nat) : State := match i with | 0 => state12_977 | 1 => state12_978 | 2 => state12_979 | 3 => state12_980 | _ => state12_981

def stree12LRRLRLLL (i : Nat) : State := if i < 4 then stree12LRRLRLLLL i else stree12LRRLRLLLR (i - 4)

def stree12LRRLRLLRL (i : Nat) : State := match i with | 0 => state12_982 | 1 => state12_983 | 2 => state12_984 | _ => state12_985

def stree12LRRLRLLRR (i : Nat) : State := match i with | 0 => state12_986 | 1 => state12_987 | 2 => state12_988 | 3 => state12_989 | _ => state12_990

def stree12LRRLRLLR (i : Nat) : State := if i < 4 then stree12LRRLRLLRL i else stree12LRRLRLLRR (i - 4)

def stree12LRRLRLL (i : Nat) : State := if i < 9 then stree12LRRLRLLL i else stree12LRRLRLLR (i - 9)

def stree12LRRLRLRLL (i : Nat) : State := match i with | 0 => state12_991 | 1 => state12_992 | 2 => state12_993 | _ => state12_994

def stree12LRRLRLRLR (i : Nat) : State := match i with | 0 => state12_995 | 1 => state12_996 | 2 => state12_997 | 3 => state12_998 | _ => state12_999

def stree12LRRLRLRL (i : Nat) : State := if i < 4 then stree12LRRLRLRLL i else stree12LRRLRLRLR (i - 4)

def stree12LRRLRLRRL (i : Nat) : State := match i with | 0 => state12_1000 | 1 => state12_1001 | 2 => state12_1002 | 3 => state12_1003 | _ => state12_1004

def stree12LRRLRLRRR (i : Nat) : State := match i with | 0 => state12_1005 | 1 => state12_1006 | 2 => state12_1007 | 3 => state12_1008 | _ => state12_1009

def stree12LRRLRLRR (i : Nat) : State := if i < 5 then stree12LRRLRLRRL i else stree12LRRLRLRRR (i - 5)

def stree12LRRLRLR (i : Nat) : State := if i < 9 then stree12LRRLRLRL i else stree12LRRLRLRR (i - 9)

def stree12LRRLRL (i : Nat) : State := if i < 18 then stree12LRRLRLL i else stree12LRRLRLR (i - 18)

def stree12LRRLRRLLL (i : Nat) : State := match i with | 0 => state12_1010 | 1 => state12_1011 | 2 => state12_1012 | _ => state12_1013

def stree12LRRLRRLLR (i : Nat) : State := match i with | 0 => state12_1014 | 1 => state12_1015 | 2 => state12_1016 | 3 => state12_1017 | _ => state12_1018

def stree12LRRLRRLL (i : Nat) : State := if i < 4 then stree12LRRLRRLLL i else stree12LRRLRRLLR (i - 4)

def stree12LRRLRRLRL (i : Nat) : State := match i with | 0 => state12_1019 | 1 => state12_1020 | 2 => state12_1021 | 3 => state12_1022 | _ => state12_1023

def stree12LRRLRRLRR (i : Nat) : State := match i with | 0 => state12_1024 | 1 => state12_1025 | 2 => state12_1026 | 3 => state12_1027 | _ => state12_1028

def stree12LRRLRRLR (i : Nat) : State := if i < 5 then stree12LRRLRRLRL i else stree12LRRLRRLRR (i - 5)

def stree12LRRLRRL (i : Nat) : State := if i < 9 then stree12LRRLRRLL i else stree12LRRLRRLR (i - 9)

def stree12LRRLRRRLL (i : Nat) : State := match i with | 0 => state12_1029 | 1 => state12_1030 | 2 => state12_1031 | _ => state12_1032

def stree12LRRLRRRLR (i : Nat) : State := match i with | 0 => state12_1033 | 1 => state12_1034 | 2 => state12_1035 | 3 => state12_1036 | _ => state12_1037

def stree12LRRLRRRL (i : Nat) : State := if i < 4 then stree12LRRLRRRLL i else stree12LRRLRRRLR (i - 4)

def stree12LRRLRRRRL (i : Nat) : State := match i with | 0 => state12_1038 | 1 => state12_1039 | 2 => state12_1040 | 3 => state12_1041 | _ => state12_1042

def stree12LRRLRRRRR (i : Nat) : State := match i with | 0 => state12_1043 | 1 => state12_1044 | 2 => state12_1045 | 3 => state12_1046 | _ => state12_1047

def stree12LRRLRRRR (i : Nat) : State := if i < 5 then stree12LRRLRRRRL i else stree12LRRLRRRRR (i - 5)

def stree12LRRLRRR (i : Nat) : State := if i < 9 then stree12LRRLRRRL i else stree12LRRLRRRR (i - 9)

def stree12LRRLRR (i : Nat) : State := if i < 19 then stree12LRRLRRL i else stree12LRRLRRR (i - 19)

def stree12LRRLR (i : Nat) : State := if i < 37 then stree12LRRLRL i else stree12LRRLRR (i - 37)

def stree12LRRL (i : Nat) : State := if i < 75 then stree12LRRLL i else stree12LRRLR (i - 75)

def stree12LRRRLLLLL (i : Nat) : State := match i with | 0 => state12_1048 | 1 => state12_1049 | 2 => state12_1050 | _ => state12_1051

def stree12LRRRLLLLR (i : Nat) : State := match i with | 0 => state12_1052 | 1 => state12_1053 | 2 => state12_1054 | 3 => state12_1055 | _ => state12_1056

def stree12LRRRLLLL (i : Nat) : State := if i < 4 then stree12LRRRLLLLL i else stree12LRRRLLLLR (i - 4)

def stree12LRRRLLLRL (i : Nat) : State := match i with | 0 => state12_1057 | 1 => state12_1058 | 2 => state12_1059 | _ => state12_1060

def stree12LRRRLLLRR (i : Nat) : State := match i with | 0 => state12_1061 | 1 => state12_1062 | 2 => state12_1063 | 3 => state12_1064 | _ => state12_1065

def stree12LRRRLLLR (i : Nat) : State := if i < 4 then stree12LRRRLLLRL i else stree12LRRRLLLRR (i - 4)

def stree12LRRRLLL (i : Nat) : State := if i < 9 then stree12LRRRLLLL i else stree12LRRRLLLR (i - 9)

def stree12LRRRLLRLL (i : Nat) : State := match i with | 0 => state12_1066 | 1 => state12_1067 | 2 => state12_1068 | _ => state12_1069

def stree12LRRRLLRLR (i : Nat) : State := match i with | 0 => state12_1070 | 1 => state12_1071 | 2 => state12_1072 | 3 => state12_1073 | _ => state12_1074

def stree12LRRRLLRL (i : Nat) : State := if i < 4 then stree12LRRRLLRLL i else stree12LRRRLLRLR (i - 4)

def stree12LRRRLLRRL (i : Nat) : State := match i with | 0 => state12_1075 | 1 => state12_1076 | 2 => state12_1077 | 3 => state12_1078 | _ => state12_1079

def stree12LRRRLLRRR (i : Nat) : State := match i with | 0 => state12_1080 | 1 => state12_1081 | 2 => state12_1082 | 3 => state12_1083 | _ => state12_1084

def stree12LRRRLLRR (i : Nat) : State := if i < 5 then stree12LRRRLLRRL i else stree12LRRRLLRRR (i - 5)

def stree12LRRRLLR (i : Nat) : State := if i < 9 then stree12LRRRLLRL i else stree12LRRRLLRR (i - 9)

def stree12LRRRLL (i : Nat) : State := if i < 18 then stree12LRRRLLL i else stree12LRRRLLR (i - 18)

def stree12LRRRLRLLL (i : Nat) : State := match i with | 0 => state12_1085 | 1 => state12_1086 | 2 => state12_1087 | _ => state12_1088

def stree12LRRRLRLLR (i : Nat) : State := match i with | 0 => state12_1089 | 1 => state12_1090 | 2 => state12_1091 | 3 => state12_1092 | _ => state12_1093

def stree12LRRRLRLL (i : Nat) : State := if i < 4 then stree12LRRRLRLLL i else stree12LRRRLRLLR (i - 4)

def stree12LRRRLRLRL (i : Nat) : State := match i with | 0 => state12_1094 | 1 => state12_1095 | 2 => state12_1096 | 3 => state12_1097 | _ => state12_1098

def stree12LRRRLRLRR (i : Nat) : State := match i with | 0 => state12_1099 | 1 => state12_1100 | 2 => state12_1101 | 3 => state12_1102 | _ => state12_1103

def stree12LRRRLRLR (i : Nat) : State := if i < 5 then stree12LRRRLRLRL i else stree12LRRRLRLRR (i - 5)

def stree12LRRRLRL (i : Nat) : State := if i < 9 then stree12LRRRLRLL i else stree12LRRRLRLR (i - 9)

def stree12LRRRLRRLL (i : Nat) : State := match i with | 0 => state12_1104 | 1 => state12_1105 | 2 => state12_1106 | _ => state12_1107

def stree12LRRRLRRLR (i : Nat) : State := match i with | 0 => state12_1108 | 1 => state12_1109 | 2 => state12_1110 | 3 => state12_1111 | _ => state12_1112

def stree12LRRRLRRL (i : Nat) : State := if i < 4 then stree12LRRRLRRLL i else stree12LRRRLRRLR (i - 4)

def stree12LRRRLRRRL (i : Nat) : State := match i with | 0 => state12_1113 | 1 => state12_1114 | 2 => state12_1115 | 3 => state12_1116 | _ => state12_1117

def stree12LRRRLRRRR (i : Nat) : State := match i with | 0 => state12_1118 | 1 => state12_1119 | 2 => state12_1120 | 3 => state12_1121 | _ => state12_1122

def stree12LRRRLRRR (i : Nat) : State := if i < 5 then stree12LRRRLRRRL i else stree12LRRRLRRRR (i - 5)

def stree12LRRRLRR (i : Nat) : State := if i < 9 then stree12LRRRLRRL i else stree12LRRRLRRR (i - 9)

def stree12LRRRLR (i : Nat) : State := if i < 19 then stree12LRRRLRL i else stree12LRRRLRR (i - 19)

def stree12LRRRL (i : Nat) : State := if i < 37 then stree12LRRRLL i else stree12LRRRLR (i - 37)

def stree12LRRRRLLLL (i : Nat) : State := match i with | 0 => state12_1123 | 1 => state12_1124 | 2 => state12_1125 | _ => state12_1126

def stree12LRRRRLLLR (i : Nat) : State := match i with | 0 => state12_1127 | 1 => state12_1128 | 2 => state12_1129 | 3 => state12_1130 | _ => state12_1131

def stree12LRRRRLLL (i : Nat) : State := if i < 4 then stree12LRRRRLLLL i else stree12LRRRRLLLR (i - 4)

def stree12LRRRRLLRL (i : Nat) : State := match i with | 0 => state12_1132 | 1 => state12_1133 | 2 => state12_1134 | _ => state12_1135

def stree12LRRRRLLRR (i : Nat) : State := match i with | 0 => state12_1136 | 1 => state12_1137 | 2 => state12_1138 | 3 => state12_1139 | _ => state12_1140

def stree12LRRRRLLR (i : Nat) : State := if i < 4 then stree12LRRRRLLRL i else stree12LRRRRLLRR (i - 4)

def stree12LRRRRLL (i : Nat) : State := if i < 9 then stree12LRRRRLLL i else stree12LRRRRLLR (i - 9)

def stree12LRRRRLRLL (i : Nat) : State := match i with | 0 => state12_1141 | 1 => state12_1142 | 2 => state12_1143 | _ => state12_1144

def stree12LRRRRLRLR (i : Nat) : State := match i with | 0 => state12_1145 | 1 => state12_1146 | 2 => state12_1147 | 3 => state12_1148 | _ => state12_1149

def stree12LRRRRLRL (i : Nat) : State := if i < 4 then stree12LRRRRLRLL i else stree12LRRRRLRLR (i - 4)

def stree12LRRRRLRRL (i : Nat) : State := match i with | 0 => state12_1150 | 1 => state12_1151 | 2 => state12_1152 | 3 => state12_1153 | _ => state12_1154

def stree12LRRRRLRRR (i : Nat) : State := match i with | 0 => state12_1155 | 1 => state12_1156 | 2 => state12_1157 | 3 => state12_1158 | _ => state12_1159

def stree12LRRRRLRR (i : Nat) : State := if i < 5 then stree12LRRRRLRRL i else stree12LRRRRLRRR (i - 5)

def stree12LRRRRLR (i : Nat) : State := if i < 9 then stree12LRRRRLRL i else stree12LRRRRLRR (i - 9)

def stree12LRRRRL (i : Nat) : State := if i < 18 then stree12LRRRRLL i else stree12LRRRRLR (i - 18)

def stree12LRRRRRLLL (i : Nat) : State := match i with | 0 => state12_1160 | 1 => state12_1161 | 2 => state12_1162 | _ => state12_1163

def stree12LRRRRRLLR (i : Nat) : State := match i with | 0 => state12_1164 | 1 => state12_1165 | 2 => state12_1166 | 3 => state12_1167 | _ => state12_1168

def stree12LRRRRRLL (i : Nat) : State := if i < 4 then stree12LRRRRRLLL i else stree12LRRRRRLLR (i - 4)

def stree12LRRRRRLRL (i : Nat) : State := match i with | 0 => state12_1169 | 1 => state12_1170 | 2 => state12_1171 | 3 => state12_1172 | _ => state12_1173

def stree12LRRRRRLRR (i : Nat) : State := match i with | 0 => state12_1174 | 1 => state12_1175 | 2 => state12_1176 | 3 => state12_1177 | _ => state12_1178

def stree12LRRRRRLR (i : Nat) : State := if i < 5 then stree12LRRRRRLRL i else stree12LRRRRRLRR (i - 5)

def stree12LRRRRRL (i : Nat) : State := if i < 9 then stree12LRRRRRLL i else stree12LRRRRRLR (i - 9)

def stree12LRRRRRRLL (i : Nat) : State := match i with | 0 => state12_1179 | 1 => state12_1180 | 2 => state12_1181 | _ => state12_1182

def stree12LRRRRRRLR (i : Nat) : State := match i with | 0 => state12_1183 | 1 => state12_1184 | 2 => state12_1185 | 3 => state12_1186 | _ => state12_1187

def stree12LRRRRRRL (i : Nat) : State := if i < 4 then stree12LRRRRRRLL i else stree12LRRRRRRLR (i - 4)

def stree12LRRRRRRRL (i : Nat) : State := match i with | 0 => state12_1188 | 1 => state12_1189 | 2 => state12_1190 | 3 => state12_1191 | _ => state12_1192

def stree12LRRRRRRRR (i : Nat) : State := match i with | 0 => state12_1193 | 1 => state12_1194 | 2 => state12_1195 | 3 => state12_1196 | _ => state12_1197

def stree12LRRRRRRR (i : Nat) : State := if i < 5 then stree12LRRRRRRRL i else stree12LRRRRRRRR (i - 5)

def stree12LRRRRRR (i : Nat) : State := if i < 9 then stree12LRRRRRRL i else stree12LRRRRRRR (i - 9)

def stree12LRRRRR (i : Nat) : State := if i < 19 then stree12LRRRRRL i else stree12LRRRRRR (i - 19)

def stree12LRRRR (i : Nat) : State := if i < 37 then stree12LRRRRL i else stree12LRRRRR (i - 37)

def stree12LRRR (i : Nat) : State := if i < 75 then stree12LRRRL i else stree12LRRRR (i - 75)

def stree12LRR (i : Nat) : State := if i < 150 then stree12LRRL i else stree12LRRR (i - 150)

def stree12LR (i : Nat) : State := if i < 299 then stree12LRL i else stree12LRR (i - 299)

def stree12L (i : Nat) : State := if i < 599 then stree12LL i else stree12LR (i - 599)

def stree12RLLLLLLLL (i : Nat) : State := match i with | 0 => state12_1198 | 1 => state12_1199 | 2 => state12_1200 | _ => state12_1201

def stree12RLLLLLLLR (i : Nat) : State := match i with | 0 => state12_1202 | 1 => state12_1203 | 2 => state12_1204 | 3 => state12_1205 | _ => state12_1206

def stree12RLLLLLLL (i : Nat) : State := if i < 4 then stree12RLLLLLLLL i else stree12RLLLLLLLR (i - 4)

def stree12RLLLLLLRL (i : Nat) : State := match i with | 0 => state12_1207 | 1 => state12_1208 | 2 => state12_1209 | _ => state12_1210

def stree12RLLLLLLRR (i : Nat) : State := match i with | 0 => state12_1211 | 1 => state12_1212 | 2 => state12_1213 | 3 => state12_1214 | _ => state12_1215

def stree12RLLLLLLR (i : Nat) : State := if i < 4 then stree12RLLLLLLRL i else stree12RLLLLLLRR (i - 4)

def stree12RLLLLLL (i : Nat) : State := if i < 9 then stree12RLLLLLLL i else stree12RLLLLLLR (i - 9)

def stree12RLLLLLRLL (i : Nat) : State := match i with | 0 => state12_1216 | 1 => state12_1217 | 2 => state12_1218 | _ => state12_1219

def stree12RLLLLLRLR (i : Nat) : State := match i with | 0 => state12_1220 | 1 => state12_1221 | 2 => state12_1222 | 3 => state12_1223 | _ => state12_1224

def stree12RLLLLLRL (i : Nat) : State := if i < 4 then stree12RLLLLLRLL i else stree12RLLLLLRLR (i - 4)

def stree12RLLLLLRRL (i : Nat) : State := match i with | 0 => state12_1225 | 1 => state12_1226 | 2 => state12_1227 | 3 => state12_1228 | _ => state12_1229

def stree12RLLLLLRRR (i : Nat) : State := match i with | 0 => state12_1230 | 1 => state12_1231 | 2 => state12_1232 | 3 => state12_1233 | _ => state12_1234

def stree12RLLLLLRR (i : Nat) : State := if i < 5 then stree12RLLLLLRRL i else stree12RLLLLLRRR (i - 5)

def stree12RLLLLLR (i : Nat) : State := if i < 9 then stree12RLLLLLRL i else stree12RLLLLLRR (i - 9)

def stree12RLLLLL (i : Nat) : State := if i < 18 then stree12RLLLLLL i else stree12RLLLLLR (i - 18)

def stree12RLLLLRLLL (i : Nat) : State := match i with | 0 => state12_1235 | 1 => state12_1236 | 2 => state12_1237 | _ => state12_1238

def stree12RLLLLRLLR (i : Nat) : State := match i with | 0 => state12_1239 | 1 => state12_1240 | 2 => state12_1241 | 3 => state12_1242 | _ => state12_1243

def stree12RLLLLRLL (i : Nat) : State := if i < 4 then stree12RLLLLRLLL i else stree12RLLLLRLLR (i - 4)

def stree12RLLLLRLRL (i : Nat) : State := match i with | 0 => state12_1244 | 1 => state12_1245 | 2 => state12_1246 | _ => state12_1247

def stree12RLLLLRLRR (i : Nat) : State := match i with | 0 => state12_1248 | 1 => state12_1249 | 2 => state12_1250 | 3 => state12_1251 | _ => state12_1252

def stree12RLLLLRLR (i : Nat) : State := if i < 4 then stree12RLLLLRLRL i else stree12RLLLLRLRR (i - 4)

def stree12RLLLLRL (i : Nat) : State := if i < 9 then stree12RLLLLRLL i else stree12RLLLLRLR (i - 9)

def stree12RLLLLRRLL (i : Nat) : State := match i with | 0 => state12_1253 | 1 => state12_1254 | 2 => state12_1255 | _ => state12_1256

def stree12RLLLLRRLR (i : Nat) : State := match i with | 0 => state12_1257 | 1 => state12_1258 | 2 => state12_1259 | 3 => state12_1260 | _ => state12_1261

def stree12RLLLLRRL (i : Nat) : State := if i < 4 then stree12RLLLLRRLL i else stree12RLLLLRRLR (i - 4)

def stree12RLLLLRRRL (i : Nat) : State := match i with | 0 => state12_1262 | 1 => state12_1263 | 2 => state12_1264 | 3 => state12_1265 | _ => state12_1266

def stree12RLLLLRRRR (i : Nat) : State := match i with | 0 => state12_1267 | 1 => state12_1268 | 2 => state12_1269 | 3 => state12_1270 | _ => state12_1271

def stree12RLLLLRRR (i : Nat) : State := if i < 5 then stree12RLLLLRRRL i else stree12RLLLLRRRR (i - 5)

def stree12RLLLLRR (i : Nat) : State := if i < 9 then stree12RLLLLRRL i else stree12RLLLLRRR (i - 9)

def stree12RLLLLR (i : Nat) : State := if i < 18 then stree12RLLLLRL i else stree12RLLLLRR (i - 18)

def stree12RLLLL (i : Nat) : State := if i < 37 then stree12RLLLLL i else stree12RLLLLR (i - 37)

def stree12RLLLRLLLL (i : Nat) : State := match i with | 0 => state12_1272 | 1 => state12_1273 | 2 => state12_1274 | _ => state12_1275

def stree12RLLLRLLLR (i : Nat) : State := match i with | 0 => state12_1276 | 1 => state12_1277 | 2 => state12_1278 | 3 => state12_1279 | _ => state12_1280

def stree12RLLLRLLL (i : Nat) : State := if i < 4 then stree12RLLLRLLLL i else stree12RLLLRLLLR (i - 4)

def stree12RLLLRLLRL (i : Nat) : State := match i with | 0 => state12_1281 | 1 => state12_1282 | 2 => state12_1283 | _ => state12_1284

def stree12RLLLRLLRR (i : Nat) : State := match i with | 0 => state12_1285 | 1 => state12_1286 | 2 => state12_1287 | 3 => state12_1288 | _ => state12_1289

def stree12RLLLRLLR (i : Nat) : State := if i < 4 then stree12RLLLRLLRL i else stree12RLLLRLLRR (i - 4)

def stree12RLLLRLL (i : Nat) : State := if i < 9 then stree12RLLLRLLL i else stree12RLLLRLLR (i - 9)

def stree12RLLLRLRLL (i : Nat) : State := match i with | 0 => state12_1290 | 1 => state12_1291 | 2 => state12_1292 | _ => state12_1293

def stree12RLLLRLRLR (i : Nat) : State := match i with | 0 => state12_1294 | 1 => state12_1295 | 2 => state12_1296 | 3 => state12_1297 | _ => state12_1298

def stree12RLLLRLRL (i : Nat) : State := if i < 4 then stree12RLLLRLRLL i else stree12RLLLRLRLR (i - 4)

def stree12RLLLRLRRL (i : Nat) : State := match i with | 0 => state12_1299 | 1 => state12_1300 | 2 => state12_1301 | 3 => state12_1302 | _ => state12_1303

def stree12RLLLRLRRR (i : Nat) : State := match i with | 0 => state12_1304 | 1 => state12_1305 | 2 => state12_1306 | 3 => state12_1307 | _ => state12_1308

def stree12RLLLRLRR (i : Nat) : State := if i < 5 then stree12RLLLRLRRL i else stree12RLLLRLRRR (i - 5)

def stree12RLLLRLR (i : Nat) : State := if i < 9 then stree12RLLLRLRL i else stree12RLLLRLRR (i - 9)

def stree12RLLLRL (i : Nat) : State := if i < 18 then stree12RLLLRLL i else stree12RLLLRLR (i - 18)

def stree12RLLLRRLLL (i : Nat) : State := match i with | 0 => state12_1309 | 1 => state12_1310 | 2 => state12_1311 | _ => state12_1312

def stree12RLLLRRLLR (i : Nat) : State := match i with | 0 => state12_1313 | 1 => state12_1314 | 2 => state12_1315 | 3 => state12_1316 | _ => state12_1317

def stree12RLLLRRLL (i : Nat) : State := if i < 4 then stree12RLLLRRLLL i else stree12RLLLRRLLR (i - 4)

def stree12RLLLRRLRL (i : Nat) : State := match i with | 0 => state12_1318 | 1 => state12_1319 | 2 => state12_1320 | 3 => state12_1321 | _ => state12_1322

def stree12RLLLRRLRR (i : Nat) : State := match i with | 0 => state12_1323 | 1 => state12_1324 | 2 => state12_1325 | 3 => state12_1326 | _ => state12_1327

def stree12RLLLRRLR (i : Nat) : State := if i < 5 then stree12RLLLRRLRL i else stree12RLLLRRLRR (i - 5)

def stree12RLLLRRL (i : Nat) : State := if i < 9 then stree12RLLLRRLL i else stree12RLLLRRLR (i - 9)

def stree12RLLLRRRLL (i : Nat) : State := match i with | 0 => state12_1328 | 1 => state12_1329 | 2 => state12_1330 | _ => state12_1331

def stree12RLLLRRRLR (i : Nat) : State := match i with | 0 => state12_1332 | 1 => state12_1333 | 2 => state12_1334 | 3 => state12_1335 | _ => state12_1336

def stree12RLLLRRRL (i : Nat) : State := if i < 4 then stree12RLLLRRRLL i else stree12RLLLRRRLR (i - 4)

def stree12RLLLRRRRL (i : Nat) : State := match i with | 0 => state12_1337 | 1 => state12_1338 | 2 => state12_1339 | 3 => state12_1340 | _ => state12_1341

def stree12RLLLRRRRR (i : Nat) : State := match i with | 0 => state12_1342 | 1 => state12_1343 | 2 => state12_1344 | 3 => state12_1345 | _ => state12_1346

def stree12RLLLRRRR (i : Nat) : State := if i < 5 then stree12RLLLRRRRL i else stree12RLLLRRRRR (i - 5)

def stree12RLLLRRR (i : Nat) : State := if i < 9 then stree12RLLLRRRL i else stree12RLLLRRRR (i - 9)

def stree12RLLLRR (i : Nat) : State := if i < 19 then stree12RLLLRRL i else stree12RLLLRRR (i - 19)

def stree12RLLLR (i : Nat) : State := if i < 37 then stree12RLLLRL i else stree12RLLLRR (i - 37)

def stree12RLLL (i : Nat) : State := if i < 74 then stree12RLLLL i else stree12RLLLR (i - 74)

def stree12RLLRLLLLL (i : Nat) : State := match i with | 0 => state12_1347 | 1 => state12_1348 | 2 => state12_1349 | _ => state12_1350

def stree12RLLRLLLLR (i : Nat) : State := match i with | 0 => state12_1351 | 1 => state12_1352 | 2 => state12_1353 | 3 => state12_1354 | _ => state12_1355

def stree12RLLRLLLL (i : Nat) : State := if i < 4 then stree12RLLRLLLLL i else stree12RLLRLLLLR (i - 4)

def stree12RLLRLLLRL (i : Nat) : State := match i with | 0 => state12_1356 | 1 => state12_1357 | 2 => state12_1358 | _ => state12_1359

def stree12RLLRLLLRR (i : Nat) : State := match i with | 0 => state12_1360 | 1 => state12_1361 | 2 => state12_1362 | 3 => state12_1363 | _ => state12_1364

def stree12RLLRLLLR (i : Nat) : State := if i < 4 then stree12RLLRLLLRL i else stree12RLLRLLLRR (i - 4)

def stree12RLLRLLL (i : Nat) : State := if i < 9 then stree12RLLRLLLL i else stree12RLLRLLLR (i - 9)

def stree12RLLRLLRLL (i : Nat) : State := match i with | 0 => state12_1365 | 1 => state12_1366 | 2 => state12_1367 | _ => state12_1368

def stree12RLLRLLRLR (i : Nat) : State := match i with | 0 => state12_1369 | 1 => state12_1370 | 2 => state12_1371 | 3 => state12_1372 | _ => state12_1373

def stree12RLLRLLRL (i : Nat) : State := if i < 4 then stree12RLLRLLRLL i else stree12RLLRLLRLR (i - 4)

def stree12RLLRLLRRL (i : Nat) : State := match i with | 0 => state12_1374 | 1 => state12_1375 | 2 => state12_1376 | 3 => state12_1377 | _ => state12_1378

def stree12RLLRLLRRR (i : Nat) : State := match i with | 0 => state12_1379 | 1 => state12_1380 | 2 => state12_1381 | 3 => state12_1382 | _ => state12_1383

def stree12RLLRLLRR (i : Nat) : State := if i < 5 then stree12RLLRLLRRL i else stree12RLLRLLRRR (i - 5)

def stree12RLLRLLR (i : Nat) : State := if i < 9 then stree12RLLRLLRL i else stree12RLLRLLRR (i - 9)

def stree12RLLRLL (i : Nat) : State := if i < 18 then stree12RLLRLLL i else stree12RLLRLLR (i - 18)

def stree12RLLRLRLLL (i : Nat) : State := match i with | 0 => state12_1384 | 1 => state12_1385 | 2 => state12_1386 | _ => state12_1387

def stree12RLLRLRLLR (i : Nat) : State := match i with | 0 => state12_1388 | 1 => state12_1389 | 2 => state12_1390 | 3 => state12_1391 | _ => state12_1392

def stree12RLLRLRLL (i : Nat) : State := if i < 4 then stree12RLLRLRLLL i else stree12RLLRLRLLR (i - 4)

def stree12RLLRLRLRL (i : Nat) : State := match i with | 0 => state12_1393 | 1 => state12_1394 | 2 => state12_1395 | 3 => state12_1396 | _ => state12_1397

def stree12RLLRLRLRR (i : Nat) : State := match i with | 0 => state12_1398 | 1 => state12_1399 | 2 => state12_1400 | 3 => state12_1401 | _ => state12_1402

def stree12RLLRLRLR (i : Nat) : State := if i < 5 then stree12RLLRLRLRL i else stree12RLLRLRLRR (i - 5)

def stree12RLLRLRL (i : Nat) : State := if i < 9 then stree12RLLRLRLL i else stree12RLLRLRLR (i - 9)

def stree12RLLRLRRLL (i : Nat) : State := match i with | 0 => state12_1403 | 1 => state12_1404 | 2 => state12_1405 | _ => state12_1406

def stree12RLLRLRRLR (i : Nat) : State := match i with | 0 => state12_1407 | 1 => state12_1408 | 2 => state12_1409 | 3 => state12_1410 | _ => state12_1411

def stree12RLLRLRRL (i : Nat) : State := if i < 4 then stree12RLLRLRRLL i else stree12RLLRLRRLR (i - 4)

def stree12RLLRLRRRL (i : Nat) : State := match i with | 0 => state12_1412 | 1 => state12_1413 | 2 => state12_1414 | 3 => state12_1415 | _ => state12_1416

def stree12RLLRLRRRR (i : Nat) : State := match i with | 0 => state12_1417 | 1 => state12_1418 | 2 => state12_1419 | 3 => state12_1420 | _ => state12_1421

def stree12RLLRLRRR (i : Nat) : State := if i < 5 then stree12RLLRLRRRL i else stree12RLLRLRRRR (i - 5)

def stree12RLLRLRR (i : Nat) : State := if i < 9 then stree12RLLRLRRL i else stree12RLLRLRRR (i - 9)

def stree12RLLRLR (i : Nat) : State := if i < 19 then stree12RLLRLRL i else stree12RLLRLRR (i - 19)

def stree12RLLRL (i : Nat) : State := if i < 37 then stree12RLLRLL i else stree12RLLRLR (i - 37)

def stree12RLLRRLLLL (i : Nat) : State := match i with | 0 => state12_1422 | 1 => state12_1423 | 2 => state12_1424 | _ => state12_1425

def stree12RLLRRLLLR (i : Nat) : State := match i with | 0 => state12_1426 | 1 => state12_1427 | 2 => state12_1428 | 3 => state12_1429 | _ => state12_1430

def stree12RLLRRLLL (i : Nat) : State := if i < 4 then stree12RLLRRLLLL i else stree12RLLRRLLLR (i - 4)

def stree12RLLRRLLRL (i : Nat) : State := match i with | 0 => state12_1431 | 1 => state12_1432 | 2 => state12_1433 | _ => state12_1434

def stree12RLLRRLLRR (i : Nat) : State := match i with | 0 => state12_1435 | 1 => state12_1436 | 2 => state12_1437 | 3 => state12_1438 | _ => state12_1439

def stree12RLLRRLLR (i : Nat) : State := if i < 4 then stree12RLLRRLLRL i else stree12RLLRRLLRR (i - 4)

def stree12RLLRRLL (i : Nat) : State := if i < 9 then stree12RLLRRLLL i else stree12RLLRRLLR (i - 9)

def stree12RLLRRLRLL (i : Nat) : State := match i with | 0 => state12_1440 | 1 => state12_1441 | 2 => state12_1442 | _ => state12_1443

def stree12RLLRRLRLR (i : Nat) : State := match i with | 0 => state12_1444 | 1 => state12_1445 | 2 => state12_1446 | 3 => state12_1447 | _ => state12_1448

def stree12RLLRRLRL (i : Nat) : State := if i < 4 then stree12RLLRRLRLL i else stree12RLLRRLRLR (i - 4)

def stree12RLLRRLRRL (i : Nat) : State := match i with | 0 => state12_1449 | 1 => state12_1450 | 2 => state12_1451 | 3 => state12_1452 | _ => state12_1453

def stree12RLLRRLRRR (i : Nat) : State := match i with | 0 => state12_1454 | 1 => state12_1455 | 2 => state12_1456 | 3 => state12_1457 | _ => state12_1458

def stree12RLLRRLRR (i : Nat) : State := if i < 5 then stree12RLLRRLRRL i else stree12RLLRRLRRR (i - 5)

def stree12RLLRRLR (i : Nat) : State := if i < 9 then stree12RLLRRLRL i else stree12RLLRRLRR (i - 9)

def stree12RLLRRL (i : Nat) : State := if i < 18 then stree12RLLRRLL i else stree12RLLRRLR (i - 18)

def stree12RLLRRRLLL (i : Nat) : State := match i with | 0 => state12_1459 | 1 => state12_1460 | 2 => state12_1461 | _ => state12_1462

def stree12RLLRRRLLR (i : Nat) : State := match i with | 0 => state12_1463 | 1 => state12_1464 | 2 => state12_1465 | 3 => state12_1466 | _ => state12_1467

def stree12RLLRRRLL (i : Nat) : State := if i < 4 then stree12RLLRRRLLL i else stree12RLLRRRLLR (i - 4)

def stree12RLLRRRLRL (i : Nat) : State := match i with | 0 => state12_1468 | 1 => state12_1469 | 2 => state12_1470 | 3 => state12_1471 | _ => state12_1472

def stree12RLLRRRLRR (i : Nat) : State := match i with | 0 => state12_1473 | 1 => state12_1474 | 2 => state12_1475 | 3 => state12_1476 | _ => state12_1477

def stree12RLLRRRLR (i : Nat) : State := if i < 5 then stree12RLLRRRLRL i else stree12RLLRRRLRR (i - 5)

def stree12RLLRRRL (i : Nat) : State := if i < 9 then stree12RLLRRRLL i else stree12RLLRRRLR (i - 9)

def stree12RLLRRRRLL (i : Nat) : State := match i with | 0 => state12_1478 | 1 => state12_1479 | 2 => state12_1480 | _ => state12_1481

def stree12RLLRRRRLR (i : Nat) : State := match i with | 0 => state12_1482 | 1 => state12_1483 | 2 => state12_1484 | 3 => state12_1485 | _ => state12_1486

def stree12RLLRRRRL (i : Nat) : State := if i < 4 then stree12RLLRRRRLL i else stree12RLLRRRRLR (i - 4)

def stree12RLLRRRRRL (i : Nat) : State := match i with | 0 => state12_1487 | 1 => state12_1488 | 2 => state12_1489 | 3 => state12_1490 | _ => state12_1491

def stree12RLLRRRRRR (i : Nat) : State := match i with | 0 => state12_1492 | 1 => state12_1493 | 2 => state12_1494 | 3 => state12_1495 | _ => state12_1496

def stree12RLLRRRRR (i : Nat) : State := if i < 5 then stree12RLLRRRRRL i else stree12RLLRRRRRR (i - 5)

def stree12RLLRRRR (i : Nat) : State := if i < 9 then stree12RLLRRRRL i else stree12RLLRRRRR (i - 9)

def stree12RLLRRR (i : Nat) : State := if i < 19 then stree12RLLRRRL i else stree12RLLRRRR (i - 19)

def stree12RLLRR (i : Nat) : State := if i < 37 then stree12RLLRRL i else stree12RLLRRR (i - 37)

def stree12RLLR (i : Nat) : State := if i < 75 then stree12RLLRL i else stree12RLLRR (i - 75)

def stree12RLL (i : Nat) : State := if i < 149 then stree12RLLL i else stree12RLLR (i - 149)

def stree12RLRLLLLLL (i : Nat) : State := match i with | 0 => state12_1497 | 1 => state12_1498 | 2 => state12_1499 | _ => state12_1500

def stree12RLRLLLLLR (i : Nat) : State := match i with | 0 => state12_1501 | 1 => state12_1502 | 2 => state12_1503 | 3 => state12_1504 | _ => state12_1505

def stree12RLRLLLLL (i : Nat) : State := if i < 4 then stree12RLRLLLLLL i else stree12RLRLLLLLR (i - 4)

def stree12RLRLLLLRL (i : Nat) : State := match i with | 0 => state12_1506 | 1 => state12_1507 | 2 => state12_1508 | _ => state12_1509

def stree12RLRLLLLRR (i : Nat) : State := match i with | 0 => state12_1510 | 1 => state12_1511 | 2 => state12_1512 | 3 => state12_1513 | _ => state12_1514

def stree12RLRLLLLR (i : Nat) : State := if i < 4 then stree12RLRLLLLRL i else stree12RLRLLLLRR (i - 4)

def stree12RLRLLLL (i : Nat) : State := if i < 9 then stree12RLRLLLLL i else stree12RLRLLLLR (i - 9)

def stree12RLRLLLRLL (i : Nat) : State := match i with | 0 => state12_1515 | 1 => state12_1516 | 2 => state12_1517 | _ => state12_1518

def stree12RLRLLLRLR (i : Nat) : State := match i with | 0 => state12_1519 | 1 => state12_1520 | 2 => state12_1521 | 3 => state12_1522 | _ => state12_1523

def stree12RLRLLLRL (i : Nat) : State := if i < 4 then stree12RLRLLLRLL i else stree12RLRLLLRLR (i - 4)

def stree12RLRLLLRRL (i : Nat) : State := match i with | 0 => state12_1524 | 1 => state12_1525 | 2 => state12_1526 | 3 => state12_1527 | _ => state12_1528

def stree12RLRLLLRRR (i : Nat) : State := match i with | 0 => state12_1529 | 1 => state12_1530 | 2 => state12_1531 | 3 => state12_1532 | _ => state12_1533

def stree12RLRLLLRR (i : Nat) : State := if i < 5 then stree12RLRLLLRRL i else stree12RLRLLLRRR (i - 5)

def stree12RLRLLLR (i : Nat) : State := if i < 9 then stree12RLRLLLRL i else stree12RLRLLLRR (i - 9)

def stree12RLRLLL (i : Nat) : State := if i < 18 then stree12RLRLLLL i else stree12RLRLLLR (i - 18)

def stree12RLRLLRLLL (i : Nat) : State := match i with | 0 => state12_1534 | 1 => state12_1535 | 2 => state12_1536 | _ => state12_1537

def stree12RLRLLRLLR (i : Nat) : State := match i with | 0 => state12_1538 | 1 => state12_1539 | 2 => state12_1540 | 3 => state12_1541 | _ => state12_1542

def stree12RLRLLRLL (i : Nat) : State := if i < 4 then stree12RLRLLRLLL i else stree12RLRLLRLLR (i - 4)

def stree12RLRLLRLRL (i : Nat) : State := match i with | 0 => state12_1543 | 1 => state12_1544 | 2 => state12_1545 | 3 => state12_1546 | _ => state12_1547

def stree12RLRLLRLRR (i : Nat) : State := match i with | 0 => state12_1548 | 1 => state12_1549 | 2 => state12_1550 | 3 => state12_1551 | _ => state12_1552

def stree12RLRLLRLR (i : Nat) : State := if i < 5 then stree12RLRLLRLRL i else stree12RLRLLRLRR (i - 5)

def stree12RLRLLRL (i : Nat) : State := if i < 9 then stree12RLRLLRLL i else stree12RLRLLRLR (i - 9)

def stree12RLRLLRRLL (i : Nat) : State := match i with | 0 => state12_1553 | 1 => state12_1554 | 2 => state12_1555 | _ => state12_1556

def stree12RLRLLRRLR (i : Nat) : State := match i with | 0 => state12_1557 | 1 => state12_1558 | 2 => state12_1559 | 3 => state12_1560 | _ => state12_1561

def stree12RLRLLRRL (i : Nat) : State := if i < 4 then stree12RLRLLRRLL i else stree12RLRLLRRLR (i - 4)

def stree12RLRLLRRRL (i : Nat) : State := match i with | 0 => state12_1562 | 1 => state12_1563 | 2 => state12_1564 | 3 => state12_1565 | _ => state12_1566

def stree12RLRLLRRRR (i : Nat) : State := match i with | 0 => state12_1567 | 1 => state12_1568 | 2 => state12_1569 | 3 => state12_1570 | _ => state12_1571

def stree12RLRLLRRR (i : Nat) : State := if i < 5 then stree12RLRLLRRRL i else stree12RLRLLRRRR (i - 5)

def stree12RLRLLRR (i : Nat) : State := if i < 9 then stree12RLRLLRRL i else stree12RLRLLRRR (i - 9)

def stree12RLRLLR (i : Nat) : State := if i < 19 then stree12RLRLLRL i else stree12RLRLLRR (i - 19)

def stree12RLRLL (i : Nat) : State := if i < 37 then stree12RLRLLL i else stree12RLRLLR (i - 37)

def stree12RLRLRLLLL (i : Nat) : State := match i with | 0 => state12_1572 | 1 => state12_1573 | 2 => state12_1574 | _ => state12_1575

def stree12RLRLRLLLR (i : Nat) : State := match i with | 0 => state12_1576 | 1 => state12_1577 | 2 => state12_1578 | 3 => state12_1579 | _ => state12_1580

def stree12RLRLRLLL (i : Nat) : State := if i < 4 then stree12RLRLRLLLL i else stree12RLRLRLLLR (i - 4)

def stree12RLRLRLLRL (i : Nat) : State := match i with | 0 => state12_1581 | 1 => state12_1582 | 2 => state12_1583 | _ => state12_1584

def stree12RLRLRLLRR (i : Nat) : State := match i with | 0 => state12_1585 | 1 => state12_1586 | 2 => state12_1587 | 3 => state12_1588 | _ => state12_1589

def stree12RLRLRLLR (i : Nat) : State := if i < 4 then stree12RLRLRLLRL i else stree12RLRLRLLRR (i - 4)

def stree12RLRLRLL (i : Nat) : State := if i < 9 then stree12RLRLRLLL i else stree12RLRLRLLR (i - 9)

end Paper2.Certificates.Q6.Coverage
