import Paper2.Certificates.Q6CoverageCompact.Layer14Part003

namespace Paper2.Certificates.Q6.Coverage

def stree14LLRRRLL (i : Nat) : State := if i < 7 then stree14LLRRRLLL i else stree14LLRRRLLR (i - 7)

def stree14LLRRRLRL (i : Nat) : State := match i with | 0 => state14_438 | 1 => state14_439 | 2 => state14_440 | 3 => state14_441 | 4 => state14_442 | 5 => state14_443 | _ => state14_444

def stree14LLRRRLRR (i : Nat) : State := match i with | 0 => state14_445 | 1 => state14_446 | 2 => state14_447 | 3 => state14_448 | 4 => state14_449 | 5 => state14_450 | 6 => state14_451 | _ => state14_452

def stree14LLRRRLR (i : Nat) : State := if i < 7 then stree14LLRRRLRL i else stree14LLRRRLRR (i - 7)

def stree14LLRRRL (i : Nat) : State := if i < 15 then stree14LLRRRLL i else stree14LLRRRLR (i - 15)

def stree14LLRRRRLL (i : Nat) : State := match i with | 0 => state14_453 | 1 => state14_454 | 2 => state14_455 | 3 => state14_456 | 4 => state14_457 | 5 => state14_458 | _ => state14_459

def stree14LLRRRRLR (i : Nat) : State := match i with | 0 => state14_460 | 1 => state14_461 | 2 => state14_462 | 3 => state14_463 | 4 => state14_464 | 5 => state14_465 | 6 => state14_466 | _ => state14_467

def stree14LLRRRRL (i : Nat) : State := if i < 7 then stree14LLRRRRLL i else stree14LLRRRRLR (i - 7)

def stree14LLRRRRRL (i : Nat) : State := match i with | 0 => state14_468 | 1 => state14_469 | 2 => state14_470 | 3 => state14_471 | 4 => state14_472 | 5 => state14_473 | 6 => state14_474 | _ => state14_475

def stree14LLRRRRRR (i : Nat) : State := match i with | 0 => state14_476 | 1 => state14_477 | 2 => state14_478 | 3 => state14_479 | 4 => state14_480 | 5 => state14_481 | 6 => state14_482 | _ => state14_483

def stree14LLRRRRR (i : Nat) : State := if i < 8 then stree14LLRRRRRL i else stree14LLRRRRRR (i - 8)

def stree14LLRRRR (i : Nat) : State := if i < 15 then stree14LLRRRRL i else stree14LLRRRRR (i - 15)

def stree14LLRRR (i : Nat) : State := if i < 30 then stree14LLRRRL i else stree14LLRRRR (i - 30)

def stree14LLRR (i : Nat) : State := if i < 60 then stree14LLRRL i else stree14LLRRR (i - 60)

def stree14LLR (i : Nat) : State := if i < 121 then stree14LLRL i else stree14LLRR (i - 121)

def stree14LL (i : Nat) : State := if i < 242 then stree14LLL i else stree14LLR (i - 242)

def stree14LRLLLLLL (i : Nat) : State := match i with | 0 => state14_484 | 1 => state14_485 | 2 => state14_486 | 3 => state14_487 | 4 => state14_488 | 5 => state14_489 | _ => state14_490

def stree14LRLLLLLR (i : Nat) : State := match i with | 0 => state14_491 | 1 => state14_492 | 2 => state14_493 | 3 => state14_494 | 4 => state14_495 | 5 => state14_496 | 6 => state14_497 | _ => state14_498

def stree14LRLLLLL (i : Nat) : State := if i < 7 then stree14LRLLLLLL i else stree14LRLLLLLR (i - 7)

def stree14LRLLLLRL (i : Nat) : State := match i with | 0 => state14_499 | 1 => state14_500 | 2 => state14_501 | 3 => state14_502 | 4 => state14_503 | 5 => state14_504 | _ => state14_505

def stree14LRLLLLRR (i : Nat) : State := match i with | 0 => state14_506 | 1 => state14_507 | 2 => state14_508 | 3 => state14_509 | 4 => state14_510 | 5 => state14_511 | 6 => state14_512 | _ => state14_513

def stree14LRLLLLR (i : Nat) : State := if i < 7 then stree14LRLLLLRL i else stree14LRLLLLRR (i - 7)

def stree14LRLLLL (i : Nat) : State := if i < 15 then stree14LRLLLLL i else stree14LRLLLLR (i - 15)

def stree14LRLLLRLL (i : Nat) : State := match i with | 0 => state14_514 | 1 => state14_515 | 2 => state14_516 | 3 => state14_517 | 4 => state14_518 | 5 => state14_519 | _ => state14_520

def stree14LRLLLRLR (i : Nat) : State := match i with | 0 => state14_521 | 1 => state14_522 | 2 => state14_523 | 3 => state14_524 | 4 => state14_525 | 5 => state14_526 | 6 => state14_527 | _ => state14_528

def stree14LRLLLRL (i : Nat) : State := if i < 7 then stree14LRLLLRLL i else stree14LRLLLRLR (i - 7)

def stree14LRLLLRRL (i : Nat) : State := match i with | 0 => state14_529 | 1 => state14_530 | 2 => state14_531 | 3 => state14_532 | 4 => state14_533 | 5 => state14_534 | _ => state14_535

def stree14LRLLLRRR (i : Nat) : State := match i with | 0 => state14_536 | 1 => state14_537 | 2 => state14_538 | 3 => state14_539 | 4 => state14_540 | 5 => state14_541 | 6 => state14_542 | _ => state14_543

def stree14LRLLLRR (i : Nat) : State := if i < 7 then stree14LRLLLRRL i else stree14LRLLLRRR (i - 7)

def stree14LRLLLR (i : Nat) : State := if i < 15 then stree14LRLLLRL i else stree14LRLLLRR (i - 15)

def stree14LRLLL (i : Nat) : State := if i < 30 then stree14LRLLLL i else stree14LRLLLR (i - 30)

def stree14LRLLRLLL (i : Nat) : State := match i with | 0 => state14_544 | 1 => state14_545 | 2 => state14_546 | 3 => state14_547 | 4 => state14_548 | 5 => state14_549 | _ => state14_550

def stree14LRLLRLLR (i : Nat) : State := match i with | 0 => state14_551 | 1 => state14_552 | 2 => state14_553 | 3 => state14_554 | 4 => state14_555 | 5 => state14_556 | 6 => state14_557 | _ => state14_558

def stree14LRLLRLL (i : Nat) : State := if i < 7 then stree14LRLLRLLL i else stree14LRLLRLLR (i - 7)

def stree14LRLLRLRL (i : Nat) : State := match i with | 0 => state14_559 | 1 => state14_560 | 2 => state14_561 | 3 => state14_562 | 4 => state14_563 | 5 => state14_564 | _ => state14_565

def stree14LRLLRLRR (i : Nat) : State := match i with | 0 => state14_566 | 1 => state14_567 | 2 => state14_568 | 3 => state14_569 | 4 => state14_570 | 5 => state14_571 | 6 => state14_572 | _ => state14_573

def stree14LRLLRLR (i : Nat) : State := if i < 7 then stree14LRLLRLRL i else stree14LRLLRLRR (i - 7)

def stree14LRLLRL (i : Nat) : State := if i < 15 then stree14LRLLRLL i else stree14LRLLRLR (i - 15)

def stree14LRLLRRLL (i : Nat) : State := match i with | 0 => state14_574 | 1 => state14_575 | 2 => state14_576 | 3 => state14_577 | 4 => state14_578 | 5 => state14_579 | _ => state14_580

def stree14LRLLRRLR (i : Nat) : State := match i with | 0 => state14_581 | 1 => state14_582 | 2 => state14_583 | 3 => state14_584 | 4 => state14_585 | 5 => state14_586 | 6 => state14_587 | _ => state14_588

def stree14LRLLRRL (i : Nat) : State := if i < 7 then stree14LRLLRRLL i else stree14LRLLRRLR (i - 7)

def stree14LRLLRRRL (i : Nat) : State := match i with | 0 => state14_589 | 1 => state14_590 | 2 => state14_591 | 3 => state14_592 | 4 => state14_593 | 5 => state14_594 | 6 => state14_595 | _ => state14_596

def stree14LRLLRRRR (i : Nat) : State := match i with | 0 => state14_597 | 1 => state14_598 | 2 => state14_599 | 3 => state14_600 | 4 => state14_601 | 5 => state14_602 | 6 => state14_603 | _ => state14_604

def stree14LRLLRRR (i : Nat) : State := if i < 8 then stree14LRLLRRRL i else stree14LRLLRRRR (i - 8)

def stree14LRLLRR (i : Nat) : State := if i < 15 then stree14LRLLRRL i else stree14LRLLRRR (i - 15)

def stree14LRLLR (i : Nat) : State := if i < 30 then stree14LRLLRL i else stree14LRLLRR (i - 30)

def stree14LRLL (i : Nat) : State := if i < 60 then stree14LRLLL i else stree14LRLLR (i - 60)

def stree14LRLRLLLL (i : Nat) : State := match i with | 0 => state14_605 | 1 => state14_606 | 2 => state14_607 | 3 => state14_608 | 4 => state14_609 | 5 => state14_610 | _ => state14_611

def stree14LRLRLLLR (i : Nat) : State := match i with | 0 => state14_612 | 1 => state14_613 | 2 => state14_614 | 3 => state14_615 | 4 => state14_616 | 5 => state14_617 | 6 => state14_618 | _ => state14_619

def stree14LRLRLLL (i : Nat) : State := if i < 7 then stree14LRLRLLLL i else stree14LRLRLLLR (i - 7)

def stree14LRLRLLRL (i : Nat) : State := match i with | 0 => state14_620 | 1 => state14_621 | 2 => state14_622 | 3 => state14_623 | 4 => state14_624 | 5 => state14_625 | _ => state14_626

def stree14LRLRLLRR (i : Nat) : State := match i with | 0 => state14_627 | 1 => state14_628 | 2 => state14_629 | 3 => state14_630 | 4 => state14_631 | 5 => state14_632 | 6 => state14_633 | _ => state14_634

def stree14LRLRLLR (i : Nat) : State := if i < 7 then stree14LRLRLLRL i else stree14LRLRLLRR (i - 7)

def stree14LRLRLL (i : Nat) : State := if i < 15 then stree14LRLRLLL i else stree14LRLRLLR (i - 15)

def stree14LRLRLRLL (i : Nat) : State := match i with | 0 => state14_635 | 1 => state14_636 | 2 => state14_637 | 3 => state14_638 | 4 => state14_639 | 5 => state14_640 | _ => state14_641

def stree14LRLRLRLR (i : Nat) : State := match i with | 0 => state14_642 | 1 => state14_643 | 2 => state14_644 | 3 => state14_645 | 4 => state14_646 | 5 => state14_647 | 6 => state14_648 | _ => state14_649

def stree14LRLRLRL (i : Nat) : State := if i < 7 then stree14LRLRLRLL i else stree14LRLRLRLR (i - 7)

def stree14LRLRLRRL (i : Nat) : State := match i with | 0 => state14_650 | 1 => state14_651 | 2 => state14_652 | 3 => state14_653 | 4 => state14_654 | 5 => state14_655 | _ => state14_656

def stree14LRLRLRRR (i : Nat) : State := match i with | 0 => state14_657 | 1 => state14_658 | 2 => state14_659 | 3 => state14_660 | 4 => state14_661 | 5 => state14_662 | 6 => state14_663 | _ => state14_664

def stree14LRLRLRR (i : Nat) : State := if i < 7 then stree14LRLRLRRL i else stree14LRLRLRRR (i - 7)

def stree14LRLRLR (i : Nat) : State := if i < 15 then stree14LRLRLRL i else stree14LRLRLRR (i - 15)

def stree14LRLRL (i : Nat) : State := if i < 30 then stree14LRLRLL i else stree14LRLRLR (i - 30)

def stree14LRLRRLLL (i : Nat) : State := match i with | 0 => state14_665 | 1 => state14_666 | 2 => state14_667 | 3 => state14_668 | 4 => state14_669 | 5 => state14_670 | _ => state14_671

def stree14LRLRRLLR (i : Nat) : State := match i with | 0 => state14_672 | 1 => state14_673 | 2 => state14_674 | 3 => state14_675 | 4 => state14_676 | 5 => state14_677 | 6 => state14_678 | _ => state14_679

def stree14LRLRRLL (i : Nat) : State := if i < 7 then stree14LRLRRLLL i else stree14LRLRRLLR (i - 7)

def stree14LRLRRLRL (i : Nat) : State := match i with | 0 => state14_680 | 1 => state14_681 | 2 => state14_682 | 3 => state14_683 | 4 => state14_684 | 5 => state14_685 | _ => state14_686

def stree14LRLRRLRR (i : Nat) : State := match i with | 0 => state14_687 | 1 => state14_688 | 2 => state14_689 | 3 => state14_690 | 4 => state14_691 | 5 => state14_692 | 6 => state14_693 | _ => state14_694

def stree14LRLRRLR (i : Nat) : State := if i < 7 then stree14LRLRRLRL i else stree14LRLRRLRR (i - 7)

def stree14LRLRRL (i : Nat) : State := if i < 15 then stree14LRLRRLL i else stree14LRLRRLR (i - 15)

def stree14LRLRRRLL (i : Nat) : State := match i with | 0 => state14_695 | 1 => state14_696 | 2 => state14_697 | 3 => state14_698 | 4 => state14_699 | 5 => state14_700 | _ => state14_701

def stree14LRLRRRLR (i : Nat) : State := match i with | 0 => state14_702 | 1 => state14_703 | 2 => state14_704 | 3 => state14_705 | 4 => state14_706 | 5 => state14_707 | 6 => state14_708 | _ => state14_709

def stree14LRLRRRL (i : Nat) : State := if i < 7 then stree14LRLRRRLL i else stree14LRLRRRLR (i - 7)

def stree14LRLRRRRL (i : Nat) : State := match i with | 0 => state14_710 | 1 => state14_711 | 2 => state14_712 | 3 => state14_713 | 4 => state14_714 | 5 => state14_715 | 6 => state14_716 | _ => state14_717

def stree14LRLRRRRR (i : Nat) : State := match i with | 0 => state14_718 | 1 => state14_719 | 2 => state14_720 | 3 => state14_721 | 4 => state14_722 | 5 => state14_723 | 6 => state14_724 | _ => state14_725

def stree14LRLRRRR (i : Nat) : State := if i < 8 then stree14LRLRRRRL i else stree14LRLRRRRR (i - 8)

def stree14LRLRRR (i : Nat) : State := if i < 15 then stree14LRLRRRL i else stree14LRLRRRR (i - 15)

def stree14LRLRR (i : Nat) : State := if i < 30 then stree14LRLRRL i else stree14LRLRRR (i - 30)

def stree14LRLR (i : Nat) : State := if i < 60 then stree14LRLRL i else stree14LRLRR (i - 60)

def stree14LRL (i : Nat) : State := if i < 121 then stree14LRLL i else stree14LRLR (i - 121)

def stree14LRRLLLLL (i : Nat) : State := match i with | 0 => state14_726 | 1 => state14_727 | 2 => state14_728 | 3 => state14_729 | 4 => state14_730 | 5 => state14_731 | _ => state14_732

def stree14LRRLLLLR (i : Nat) : State := match i with | 0 => state14_733 | 1 => state14_734 | 2 => state14_735 | 3 => state14_736 | 4 => state14_737 | 5 => state14_738 | 6 => state14_739 | _ => state14_740

def stree14LRRLLLL (i : Nat) : State := if i < 7 then stree14LRRLLLLL i else stree14LRRLLLLR (i - 7)

def stree14LRRLLLRL (i : Nat) : State := match i with | 0 => state14_741 | 1 => state14_742 | 2 => state14_743 | 3 => state14_744 | 4 => state14_745 | 5 => state14_746 | _ => state14_747

def stree14LRRLLLRR (i : Nat) : State := match i with | 0 => state14_748 | 1 => state14_749 | 2 => state14_750 | 3 => state14_751 | 4 => state14_752 | 5 => state14_753 | 6 => state14_754 | _ => state14_755

def stree14LRRLLLR (i : Nat) : State := if i < 7 then stree14LRRLLLRL i else stree14LRRLLLRR (i - 7)

def stree14LRRLLL (i : Nat) : State := if i < 15 then stree14LRRLLLL i else stree14LRRLLLR (i - 15)

def stree14LRRLLRLL (i : Nat) : State := match i with | 0 => state14_756 | 1 => state14_757 | 2 => state14_758 | 3 => state14_759 | 4 => state14_760 | 5 => state14_761 | _ => state14_762

def stree14LRRLLRLR (i : Nat) : State := match i with | 0 => state14_763 | 1 => state14_764 | 2 => state14_765 | 3 => state14_766 | 4 => state14_767 | 5 => state14_768 | 6 => state14_769 | _ => state14_770

def stree14LRRLLRL (i : Nat) : State := if i < 7 then stree14LRRLLRLL i else stree14LRRLLRLR (i - 7)

def stree14LRRLLRRL (i : Nat) : State := match i with | 0 => state14_771 | 1 => state14_772 | 2 => state14_773 | 3 => state14_774 | 4 => state14_775 | 5 => state14_776 | _ => state14_777

def stree14LRRLLRRR (i : Nat) : State := match i with | 0 => state14_778 | 1 => state14_779 | 2 => state14_780 | 3 => state14_781 | 4 => state14_782 | 5 => state14_783 | 6 => state14_784 | _ => state14_785

def stree14LRRLLRR (i : Nat) : State := if i < 7 then stree14LRRLLRRL i else stree14LRRLLRRR (i - 7)

def stree14LRRLLR (i : Nat) : State := if i < 15 then stree14LRRLLRL i else stree14LRRLLRR (i - 15)

def stree14LRRLL (i : Nat) : State := if i < 30 then stree14LRRLLL i else stree14LRRLLR (i - 30)

def stree14LRRLRLLL (i : Nat) : State := match i with | 0 => state14_786 | 1 => state14_787 | 2 => state14_788 | 3 => state14_789 | 4 => state14_790 | 5 => state14_791 | _ => state14_792

def stree14LRRLRLLR (i : Nat) : State := match i with | 0 => state14_793 | 1 => state14_794 | 2 => state14_795 | 3 => state14_796 | 4 => state14_797 | 5 => state14_798 | 6 => state14_799 | _ => state14_800

def stree14LRRLRLL (i : Nat) : State := if i < 7 then stree14LRRLRLLL i else stree14LRRLRLLR (i - 7)

def stree14LRRLRLRL (i : Nat) : State := match i with | 0 => state14_801 | 1 => state14_802 | 2 => state14_803 | 3 => state14_804 | 4 => state14_805 | 5 => state14_806 | _ => state14_807

def stree14LRRLRLRR (i : Nat) : State := match i with | 0 => state14_808 | 1 => state14_809 | 2 => state14_810 | 3 => state14_811 | 4 => state14_812 | 5 => state14_813 | 6 => state14_814 | _ => state14_815

def stree14LRRLRLR (i : Nat) : State := if i < 7 then stree14LRRLRLRL i else stree14LRRLRLRR (i - 7)

def stree14LRRLRL (i : Nat) : State := if i < 15 then stree14LRRLRLL i else stree14LRRLRLR (i - 15)

def stree14LRRLRRLL (i : Nat) : State := match i with | 0 => state14_816 | 1 => state14_817 | 2 => state14_818 | 3 => state14_819 | 4 => state14_820 | 5 => state14_821 | _ => state14_822

def stree14LRRLRRLR (i : Nat) : State := match i with | 0 => state14_823 | 1 => state14_824 | 2 => state14_825 | 3 => state14_826 | 4 => state14_827 | 5 => state14_828 | 6 => state14_829 | _ => state14_830

def stree14LRRLRRL (i : Nat) : State := if i < 7 then stree14LRRLRRLL i else stree14LRRLRRLR (i - 7)

def stree14LRRLRRRL (i : Nat) : State := match i with | 0 => state14_831 | 1 => state14_832 | 2 => state14_833 | 3 => state14_834 | 4 => state14_835 | 5 => state14_836 | 6 => state14_837 | _ => state14_838

def stree14LRRLRRRR (i : Nat) : State := match i with | 0 => state14_839 | 1 => state14_840 | 2 => state14_841 | 3 => state14_842 | 4 => state14_843 | 5 => state14_844 | 6 => state14_845 | _ => state14_846

def stree14LRRLRRR (i : Nat) : State := if i < 8 then stree14LRRLRRRL i else stree14LRRLRRRR (i - 8)

def stree14LRRLRR (i : Nat) : State := if i < 15 then stree14LRRLRRL i else stree14LRRLRRR (i - 15)

def stree14LRRLR (i : Nat) : State := if i < 30 then stree14LRRLRL i else stree14LRRLRR (i - 30)

def stree14LRRL (i : Nat) : State := if i < 60 then stree14LRRLL i else stree14LRRLR (i - 60)

def stree14LRRRLLLL (i : Nat) : State := match i with | 0 => state14_847 | 1 => state14_848 | 2 => state14_849 | 3 => state14_850 | 4 => state14_851 | 5 => state14_852 | _ => state14_853

def stree14LRRRLLLR (i : Nat) : State := match i with | 0 => state14_854 | 1 => state14_855 | 2 => state14_856 | 3 => state14_857 | 4 => state14_858 | 5 => state14_859 | 6 => state14_860 | _ => state14_861

def stree14LRRRLLL (i : Nat) : State := if i < 7 then stree14LRRRLLLL i else stree14LRRRLLLR (i - 7)

def stree14LRRRLLRL (i : Nat) : State := match i with | 0 => state14_862 | 1 => state14_863 | 2 => state14_864 | 3 => state14_865 | 4 => state14_866 | 5 => state14_867 | _ => state14_868

def stree14LRRRLLRR (i : Nat) : State := match i with | 0 => state14_869 | 1 => state14_870 | 2 => state14_871 | 3 => state14_872 | 4 => state14_873 | 5 => state14_874 | 6 => state14_875 | _ => state14_876

def stree14LRRRLLR (i : Nat) : State := if i < 7 then stree14LRRRLLRL i else stree14LRRRLLRR (i - 7)

def stree14LRRRLL (i : Nat) : State := if i < 15 then stree14LRRRLLL i else stree14LRRRLLR (i - 15)

def stree14LRRRLRLL (i : Nat) : State := match i with | 0 => state14_877 | 1 => state14_878 | 2 => state14_879 | 3 => state14_880 | 4 => state14_881 | 5 => state14_882 | _ => state14_883

def stree14LRRRLRLR (i : Nat) : State := match i with | 0 => state14_884 | 1 => state14_885 | 2 => state14_886 | 3 => state14_887 | 4 => state14_888 | 5 => state14_889 | 6 => state14_890 | _ => state14_891

def stree14LRRRLRL (i : Nat) : State := if i < 7 then stree14LRRRLRLL i else stree14LRRRLRLR (i - 7)

def stree14LRRRLRRL (i : Nat) : State := match i with | 0 => state14_892 | 1 => state14_893 | 2 => state14_894 | 3 => state14_895 | 4 => state14_896 | 5 => state14_897 | _ => state14_898

def stree14LRRRLRRR (i : Nat) : State := match i with | 0 => state14_899 | 1 => state14_900 | 2 => state14_901 | 3 => state14_902 | 4 => state14_903 | 5 => state14_904 | 6 => state14_905 | _ => state14_906

def stree14LRRRLRR (i : Nat) : State := if i < 7 then stree14LRRRLRRL i else stree14LRRRLRRR (i - 7)

def stree14LRRRLR (i : Nat) : State := if i < 15 then stree14LRRRLRL i else stree14LRRRLRR (i - 15)

def stree14LRRRL (i : Nat) : State := if i < 30 then stree14LRRRLL i else stree14LRRRLR (i - 30)

def stree14LRRRRLLL (i : Nat) : State := match i with | 0 => state14_907 | 1 => state14_908 | 2 => state14_909 | 3 => state14_910 | 4 => state14_911 | 5 => state14_912 | _ => state14_913

def stree14LRRRRLLR (i : Nat) : State := match i with | 0 => state14_914 | 1 => state14_915 | 2 => state14_916 | 3 => state14_917 | 4 => state14_918 | 5 => state14_919 | 6 => state14_920 | _ => state14_921

def stree14LRRRRLL (i : Nat) : State := if i < 7 then stree14LRRRRLLL i else stree14LRRRRLLR (i - 7)

def stree14LRRRRLRL (i : Nat) : State := match i with | 0 => state14_922 | 1 => state14_923 | 2 => state14_924 | 3 => state14_925 | 4 => state14_926 | 5 => state14_927 | _ => state14_928

def stree14LRRRRLRR (i : Nat) : State := match i with | 0 => state14_929 | 1 => state14_930 | 2 => state14_931 | 3 => state14_932 | 4 => state14_933 | 5 => state14_934 | 6 => state14_935 | _ => state14_936

def stree14LRRRRLR (i : Nat) : State := if i < 7 then stree14LRRRRLRL i else stree14LRRRRLRR (i - 7)

def stree14LRRRRL (i : Nat) : State := if i < 15 then stree14LRRRRLL i else stree14LRRRRLR (i - 15)

def stree14LRRRRRLL (i : Nat) : State := match i with | 0 => state14_937 | 1 => state14_938 | 2 => state14_939 | 3 => state14_940 | 4 => state14_941 | 5 => state14_942 | _ => state14_943

def stree14LRRRRRLR (i : Nat) : State := match i with | 0 => state14_944 | 1 => state14_945 | 2 => state14_946 | 3 => state14_947 | 4 => state14_948 | 5 => state14_949 | 6 => state14_950 | _ => state14_951

def stree14LRRRRRL (i : Nat) : State := if i < 7 then stree14LRRRRRLL i else stree14LRRRRRLR (i - 7)

def stree14LRRRRRRL (i : Nat) : State := match i with | 0 => state14_952 | 1 => state14_953 | 2 => state14_954 | 3 => state14_955 | 4 => state14_956 | 5 => state14_957 | 6 => state14_958 | _ => state14_959

def stree14LRRRRRRR (i : Nat) : State := match i with | 0 => state14_960 | 1 => state14_961 | 2 => state14_962 | 3 => state14_963 | 4 => state14_964 | 5 => state14_965 | 6 => state14_966 | _ => state14_967

def stree14LRRRRRR (i : Nat) : State := if i < 8 then stree14LRRRRRRL i else stree14LRRRRRRR (i - 8)

def stree14LRRRRR (i : Nat) : State := if i < 15 then stree14LRRRRRL i else stree14LRRRRRR (i - 15)

def stree14LRRRR (i : Nat) : State := if i < 30 then stree14LRRRRL i else stree14LRRRRR (i - 30)

def stree14LRRR (i : Nat) : State := if i < 60 then stree14LRRRL i else stree14LRRRR (i - 60)

def stree14LRR (i : Nat) : State := if i < 121 then stree14LRRL i else stree14LRRR (i - 121)

def stree14LR (i : Nat) : State := if i < 242 then stree14LRL i else stree14LRR (i - 242)

def stree14L (i : Nat) : State := if i < 484 then stree14LL i else stree14LR (i - 484)

def stree14RLLLLLLL (i : Nat) : State := match i with | 0 => state14_968 | 1 => state14_969 | 2 => state14_970 | 3 => state14_971 | 4 => state14_972 | 5 => state14_973 | _ => state14_974

def stree14RLLLLLLR (i : Nat) : State := match i with | 0 => state14_975 | 1 => state14_976 | 2 => state14_977 | 3 => state14_978 | 4 => state14_979 | 5 => state14_980 | 6 => state14_981 | _ => state14_982

def stree14RLLLLLL (i : Nat) : State := if i < 7 then stree14RLLLLLLL i else stree14RLLLLLLR (i - 7)

def stree14RLLLLLRL (i : Nat) : State := match i with | 0 => state14_983 | 1 => state14_984 | 2 => state14_985 | 3 => state14_986 | 4 => state14_987 | 5 => state14_988 | _ => state14_989

def stree14RLLLLLRR (i : Nat) : State := match i with | 0 => state14_990 | 1 => state14_991 | 2 => state14_992 | 3 => state14_993 | 4 => state14_994 | 5 => state14_995 | 6 => state14_996 | _ => state14_997

def stree14RLLLLLR (i : Nat) : State := if i < 7 then stree14RLLLLLRL i else stree14RLLLLLRR (i - 7)

def stree14RLLLLL (i : Nat) : State := if i < 15 then stree14RLLLLLL i else stree14RLLLLLR (i - 15)

def stree14RLLLLRLL (i : Nat) : State := match i with | 0 => state14_998 | 1 => state14_999 | 2 => state14_1000 | 3 => state14_1001 | 4 => state14_1002 | 5 => state14_1003 | _ => state14_1004

def stree14RLLLLRLR (i : Nat) : State := match i with | 0 => state14_1005 | 1 => state14_1006 | 2 => state14_1007 | 3 => state14_1008 | 4 => state14_1009 | 5 => state14_1010 | 6 => state14_1011 | _ => state14_1012

def stree14RLLLLRL (i : Nat) : State := if i < 7 then stree14RLLLLRLL i else stree14RLLLLRLR (i - 7)

def stree14RLLLLRRL (i : Nat) : State := match i with | 0 => state14_1013 | 1 => state14_1014 | 2 => state14_1015 | 3 => state14_1016 | 4 => state14_1017 | 5 => state14_1018 | _ => state14_1019

def stree14RLLLLRRR (i : Nat) : State := match i with | 0 => state14_1020 | 1 => state14_1021 | 2 => state14_1022 | 3 => state14_1023 | 4 => state14_1024 | 5 => state14_1025 | 6 => state14_1026 | _ => state14_1027

def stree14RLLLLRR (i : Nat) : State := if i < 7 then stree14RLLLLRRL i else stree14RLLLLRRR (i - 7)

def stree14RLLLLR (i : Nat) : State := if i < 15 then stree14RLLLLRL i else stree14RLLLLRR (i - 15)

def stree14RLLLL (i : Nat) : State := if i < 30 then stree14RLLLLL i else stree14RLLLLR (i - 30)

def stree14RLLLRLLL (i : Nat) : State := match i with | 0 => state14_1028 | 1 => state14_1029 | 2 => state14_1030 | 3 => state14_1031 | 4 => state14_1032 | 5 => state14_1033 | _ => state14_1034

def stree14RLLLRLLR (i : Nat) : State := match i with | 0 => state14_1035 | 1 => state14_1036 | 2 => state14_1037 | 3 => state14_1038 | 4 => state14_1039 | 5 => state14_1040 | 6 => state14_1041 | _ => state14_1042

def stree14RLLLRLL (i : Nat) : State := if i < 7 then stree14RLLLRLLL i else stree14RLLLRLLR (i - 7)

def stree14RLLLRLRL (i : Nat) : State := match i with | 0 => state14_1043 | 1 => state14_1044 | 2 => state14_1045 | 3 => state14_1046 | 4 => state14_1047 | 5 => state14_1048 | _ => state14_1049

def stree14RLLLRLRR (i : Nat) : State := match i with | 0 => state14_1050 | 1 => state14_1051 | 2 => state14_1052 | 3 => state14_1053 | 4 => state14_1054 | 5 => state14_1055 | 6 => state14_1056 | _ => state14_1057

def stree14RLLLRLR (i : Nat) : State := if i < 7 then stree14RLLLRLRL i else stree14RLLLRLRR (i - 7)

def stree14RLLLRL (i : Nat) : State := if i < 15 then stree14RLLLRLL i else stree14RLLLRLR (i - 15)

def stree14RLLLRRLL (i : Nat) : State := match i with | 0 => state14_1058 | 1 => state14_1059 | 2 => state14_1060 | 3 => state14_1061 | 4 => state14_1062 | 5 => state14_1063 | _ => state14_1064

def stree14RLLLRRLR (i : Nat) : State := match i with | 0 => state14_1065 | 1 => state14_1066 | 2 => state14_1067 | 3 => state14_1068 | 4 => state14_1069 | 5 => state14_1070 | 6 => state14_1071 | _ => state14_1072

def stree14RLLLRRL (i : Nat) : State := if i < 7 then stree14RLLLRRLL i else stree14RLLLRRLR (i - 7)

def stree14RLLLRRRL (i : Nat) : State := match i with | 0 => state14_1073 | 1 => state14_1074 | 2 => state14_1075 | 3 => state14_1076 | 4 => state14_1077 | 5 => state14_1078 | 6 => state14_1079 | _ => state14_1080

def stree14RLLLRRRR (i : Nat) : State := match i with | 0 => state14_1081 | 1 => state14_1082 | 2 => state14_1083 | 3 => state14_1084 | 4 => state14_1085 | 5 => state14_1086 | 6 => state14_1087 | _ => state14_1088

def stree14RLLLRRR (i : Nat) : State := if i < 8 then stree14RLLLRRRL i else stree14RLLLRRRR (i - 8)

def stree14RLLLRR (i : Nat) : State := if i < 15 then stree14RLLLRRL i else stree14RLLLRRR (i - 15)

def stree14RLLLR (i : Nat) : State := if i < 30 then stree14RLLLRL i else stree14RLLLRR (i - 30)

def stree14RLLL (i : Nat) : State := if i < 60 then stree14RLLLL i else stree14RLLLR (i - 60)

def stree14RLLRLLLL (i : Nat) : State := match i with | 0 => state14_1089 | 1 => state14_1090 | 2 => state14_1091 | 3 => state14_1092 | 4 => state14_1093 | 5 => state14_1094 | _ => state14_1095

def stree14RLLRLLLR (i : Nat) : State := match i with | 0 => state14_1096 | 1 => state14_1097 | 2 => state14_1098 | 3 => state14_1099 | 4 => state14_1100 | 5 => state14_1101 | 6 => state14_1102 | _ => state14_1103

def stree14RLLRLLL (i : Nat) : State := if i < 7 then stree14RLLRLLLL i else stree14RLLRLLLR (i - 7)

def stree14RLLRLLRL (i : Nat) : State := match i with | 0 => state14_1104 | 1 => state14_1105 | 2 => state14_1106 | 3 => state14_1107 | 4 => state14_1108 | 5 => state14_1109 | _ => state14_1110

def stree14RLLRLLRR (i : Nat) : State := match i with | 0 => state14_1111 | 1 => state14_1112 | 2 => state14_1113 | 3 => state14_1114 | 4 => state14_1115 | 5 => state14_1116 | 6 => state14_1117 | _ => state14_1118

def stree14RLLRLLR (i : Nat) : State := if i < 7 then stree14RLLRLLRL i else stree14RLLRLLRR (i - 7)

def stree14RLLRLL (i : Nat) : State := if i < 15 then stree14RLLRLLL i else stree14RLLRLLR (i - 15)

def stree14RLLRLRLL (i : Nat) : State := match i with | 0 => state14_1119 | 1 => state14_1120 | 2 => state14_1121 | 3 => state14_1122 | 4 => state14_1123 | 5 => state14_1124 | _ => state14_1125

def stree14RLLRLRLR (i : Nat) : State := match i with | 0 => state14_1126 | 1 => state14_1127 | 2 => state14_1128 | 3 => state14_1129 | 4 => state14_1130 | 5 => state14_1131 | 6 => state14_1132 | _ => state14_1133

def stree14RLLRLRL (i : Nat) : State := if i < 7 then stree14RLLRLRLL i else stree14RLLRLRLR (i - 7)

def stree14RLLRLRRL (i : Nat) : State := match i with | 0 => state14_1134 | 1 => state14_1135 | 2 => state14_1136 | 3 => state14_1137 | 4 => state14_1138 | 5 => state14_1139 | _ => state14_1140

def stree14RLLRLRRR (i : Nat) : State := match i with | 0 => state14_1141 | 1 => state14_1142 | 2 => state14_1143 | 3 => state14_1144 | 4 => state14_1145 | 5 => state14_1146 | 6 => state14_1147 | _ => state14_1148

def stree14RLLRLRR (i : Nat) : State := if i < 7 then stree14RLLRLRRL i else stree14RLLRLRRR (i - 7)

def stree14RLLRLR (i : Nat) : State := if i < 15 then stree14RLLRLRL i else stree14RLLRLRR (i - 15)

def stree14RLLRL (i : Nat) : State := if i < 30 then stree14RLLRLL i else stree14RLLRLR (i - 30)

def stree14RLLRRLLL (i : Nat) : State := match i with | 0 => state14_1149 | 1 => state14_1150 | 2 => state14_1151 | 3 => state14_1152 | 4 => state14_1153 | 5 => state14_1154 | _ => state14_1155

def stree14RLLRRLLR (i : Nat) : State := match i with | 0 => state14_1156 | 1 => state14_1157 | 2 => state14_1158 | 3 => state14_1159 | 4 => state14_1160 | 5 => state14_1161 | 6 => state14_1162 | _ => state14_1163

def stree14RLLRRLL (i : Nat) : State := if i < 7 then stree14RLLRRLLL i else stree14RLLRRLLR (i - 7)

def stree14RLLRRLRL (i : Nat) : State := match i with | 0 => state14_1164 | 1 => state14_1165 | 2 => state14_1166 | 3 => state14_1167 | 4 => state14_1168 | 5 => state14_1169 | _ => state14_1170

def stree14RLLRRLRR (i : Nat) : State := match i with | 0 => state14_1171 | 1 => state14_1172 | 2 => state14_1173 | 3 => state14_1174 | 4 => state14_1175 | 5 => state14_1176 | 6 => state14_1177 | _ => state14_1178

def stree14RLLRRLR (i : Nat) : State := if i < 7 then stree14RLLRRLRL i else stree14RLLRRLRR (i - 7)

def stree14RLLRRL (i : Nat) : State := if i < 15 then stree14RLLRRLL i else stree14RLLRRLR (i - 15)

def stree14RLLRRRLL (i : Nat) : State := match i with | 0 => state14_1179 | 1 => state14_1180 | 2 => state14_1181 | 3 => state14_1182 | 4 => state14_1183 | 5 => state14_1184 | _ => state14_1185

def stree14RLLRRRLR (i : Nat) : State := match i with | 0 => state14_1186 | 1 => state14_1187 | 2 => state14_1188 | 3 => state14_1189 | 4 => state14_1190 | 5 => state14_1191 | 6 => state14_1192 | _ => state14_1193

def stree14RLLRRRL (i : Nat) : State := if i < 7 then stree14RLLRRRLL i else stree14RLLRRRLR (i - 7)

def stree14RLLRRRRL (i : Nat) : State := match i with | 0 => state14_1194 | 1 => state14_1195 | 2 => state14_1196 | 3 => state14_1197 | 4 => state14_1198 | 5 => state14_1199 | 6 => state14_1200 | _ => state14_1201

def stree14RLLRRRRR (i : Nat) : State := match i with | 0 => state14_1202 | 1 => state14_1203 | 2 => state14_1204 | 3 => state14_1205 | 4 => state14_1206 | 5 => state14_1207 | 6 => state14_1208 | _ => state14_1209

def stree14RLLRRRR (i : Nat) : State := if i < 8 then stree14RLLRRRRL i else stree14RLLRRRRR (i - 8)

def stree14RLLRRR (i : Nat) : State := if i < 15 then stree14RLLRRRL i else stree14RLLRRRR (i - 15)

def stree14RLLRR (i : Nat) : State := if i < 30 then stree14RLLRRL i else stree14RLLRRR (i - 30)

def stree14RLLR (i : Nat) : State := if i < 60 then stree14RLLRL i else stree14RLLRR (i - 60)

def stree14RLL (i : Nat) : State := if i < 121 then stree14RLLL i else stree14RLLR (i - 121)

def stree14RLRLLLLL (i : Nat) : State := match i with | 0 => state14_1210 | 1 => state14_1211 | 2 => state14_1212 | 3 => state14_1213 | 4 => state14_1214 | 5 => state14_1215 | _ => state14_1216

def stree14RLRLLLLR (i : Nat) : State := match i with | 0 => state14_1217 | 1 => state14_1218 | 2 => state14_1219 | 3 => state14_1220 | 4 => state14_1221 | 5 => state14_1222 | 6 => state14_1223 | _ => state14_1224

def stree14RLRLLLL (i : Nat) : State := if i < 7 then stree14RLRLLLLL i else stree14RLRLLLLR (i - 7)

def stree14RLRLLLRL (i : Nat) : State := match i with | 0 => state14_1225 | 1 => state14_1226 | 2 => state14_1227 | 3 => state14_1228 | 4 => state14_1229 | 5 => state14_1230 | _ => state14_1231

def stree14RLRLLLRR (i : Nat) : State := match i with | 0 => state14_1232 | 1 => state14_1233 | 2 => state14_1234 | 3 => state14_1235 | 4 => state14_1236 | 5 => state14_1237 | 6 => state14_1238 | _ => state14_1239

def stree14RLRLLLR (i : Nat) : State := if i < 7 then stree14RLRLLLRL i else stree14RLRLLLRR (i - 7)

def stree14RLRLLL (i : Nat) : State := if i < 15 then stree14RLRLLLL i else stree14RLRLLLR (i - 15)

def stree14RLRLLRLL (i : Nat) : State := match i with | 0 => state14_1240 | 1 => state14_1241 | 2 => state14_1242 | 3 => state14_1243 | 4 => state14_1244 | 5 => state14_1245 | _ => state14_1246

def stree14RLRLLRLR (i : Nat) : State := match i with | 0 => state14_1247 | 1 => state14_1248 | 2 => state14_1249 | 3 => state14_1250 | 4 => state14_1251 | 5 => state14_1252 | 6 => state14_1253 | _ => state14_1254

def stree14RLRLLRL (i : Nat) : State := if i < 7 then stree14RLRLLRLL i else stree14RLRLLRLR (i - 7)

def stree14RLRLLRRL (i : Nat) : State := match i with | 0 => state14_1255 | 1 => state14_1256 | 2 => state14_1257 | 3 => state14_1258 | 4 => state14_1259 | 5 => state14_1260 | _ => state14_1261

def stree14RLRLLRRR (i : Nat) : State := match i with | 0 => state14_1262 | 1 => state14_1263 | 2 => state14_1264 | 3 => state14_1265 | 4 => state14_1266 | 5 => state14_1267 | 6 => state14_1268 | _ => state14_1269

def stree14RLRLLRR (i : Nat) : State := if i < 7 then stree14RLRLLRRL i else stree14RLRLLRRR (i - 7)

def stree14RLRLLR (i : Nat) : State := if i < 15 then stree14RLRLLRL i else stree14RLRLLRR (i - 15)

def stree14RLRLL (i : Nat) : State := if i < 30 then stree14RLRLLL i else stree14RLRLLR (i - 30)

def stree14RLRLRLLL (i : Nat) : State := match i with | 0 => state14_1270 | 1 => state14_1271 | 2 => state14_1272 | 3 => state14_1273 | 4 => state14_1274 | 5 => state14_1275 | _ => state14_1276

def stree14RLRLRLLR (i : Nat) : State := match i with | 0 => state14_1277 | 1 => state14_1278 | 2 => state14_1279 | 3 => state14_1280 | 4 => state14_1281 | 5 => state14_1282 | 6 => state14_1283 | _ => state14_1284

def stree14RLRLRLL (i : Nat) : State := if i < 7 then stree14RLRLRLLL i else stree14RLRLRLLR (i - 7)

def stree14RLRLRLRL (i : Nat) : State := match i with | 0 => state14_1285 | 1 => state14_1286 | 2 => state14_1287 | 3 => state14_1288 | 4 => state14_1289 | 5 => state14_1290 | _ => state14_1291

def stree14RLRLRLRR (i : Nat) : State := match i with | 0 => state14_1292 | 1 => state14_1293 | 2 => state14_1294 | 3 => state14_1295 | 4 => state14_1296 | 5 => state14_1297 | 6 => state14_1298 | _ => state14_1299

def stree14RLRLRLR (i : Nat) : State := if i < 7 then stree14RLRLRLRL i else stree14RLRLRLRR (i - 7)

def stree14RLRLRL (i : Nat) : State := if i < 15 then stree14RLRLRLL i else stree14RLRLRLR (i - 15)

def stree14RLRLRRLL (i : Nat) : State := match i with | 0 => state14_1300 | 1 => state14_1301 | 2 => state14_1302 | 3 => state14_1303 | 4 => state14_1304 | 5 => state14_1305 | _ => state14_1306

def stree14RLRLRRLR (i : Nat) : State := match i with | 0 => state14_1307 | 1 => state14_1308 | 2 => state14_1309 | 3 => state14_1310 | 4 => state14_1311 | 5 => state14_1312 | 6 => state14_1313 | _ => state14_1314

def stree14RLRLRRL (i : Nat) : State := if i < 7 then stree14RLRLRRLL i else stree14RLRLRRLR (i - 7)

def stree14RLRLRRRL (i : Nat) : State := match i with | 0 => state14_1315 | 1 => state14_1316 | 2 => state14_1317 | 3 => state14_1318 | 4 => state14_1319 | 5 => state14_1320 | 6 => state14_1321 | _ => state14_1322

def stree14RLRLRRRR (i : Nat) : State := match i with | 0 => state14_1323 | 1 => state14_1324 | 2 => state14_1325 | 3 => state14_1326 | 4 => state14_1327 | 5 => state14_1328 | 6 => state14_1329 | _ => state14_1330

def stree14RLRLRRR (i : Nat) : State := if i < 8 then stree14RLRLRRRL i else stree14RLRLRRRR (i - 8)

def stree14RLRLRR (i : Nat) : State := if i < 15 then stree14RLRLRRL i else stree14RLRLRRR (i - 15)

def stree14RLRLR (i : Nat) : State := if i < 30 then stree14RLRLRL i else stree14RLRLRR (i - 30)

def stree14RLRL (i : Nat) : State := if i < 60 then stree14RLRLL i else stree14RLRLR (i - 60)

def stree14RLRRLLLL (i : Nat) : State := match i with | 0 => state14_1331 | 1 => state14_1332 | 2 => state14_1333 | 3 => state14_1334 | 4 => state14_1335 | 5 => state14_1336 | _ => state14_1337

def stree14RLRRLLLR (i : Nat) : State := match i with | 0 => state14_1338 | 1 => state14_1339 | 2 => state14_1340 | 3 => state14_1341 | 4 => state14_1342 | 5 => state14_1343 | 6 => state14_1344 | _ => state14_1345

def stree14RLRRLLL (i : Nat) : State := if i < 7 then stree14RLRRLLLL i else stree14RLRRLLLR (i - 7)

def stree14RLRRLLRL (i : Nat) : State := match i with | 0 => state14_1346 | 1 => state14_1347 | 2 => state14_1348 | 3 => state14_1349 | 4 => state14_1350 | 5 => state14_1351 | _ => state14_1352

def stree14RLRRLLRR (i : Nat) : State := match i with | 0 => state14_1353 | 1 => state14_1354 | 2 => state14_1355 | 3 => state14_1356 | 4 => state14_1357 | 5 => state14_1358 | 6 => state14_1359 | _ => state14_1360

def stree14RLRRLLR (i : Nat) : State := if i < 7 then stree14RLRRLLRL i else stree14RLRRLLRR (i - 7)

def stree14RLRRLL (i : Nat) : State := if i < 15 then stree14RLRRLLL i else stree14RLRRLLR (i - 15)

def stree14RLRRLRLL (i : Nat) : State := match i with | 0 => state14_1361 | 1 => state14_1362 | 2 => state14_1363 | 3 => state14_1364 | 4 => state14_1365 | 5 => state14_1366 | _ => state14_1367

def stree14RLRRLRLR (i : Nat) : State := match i with | 0 => state14_1368 | 1 => state14_1369 | 2 => state14_1370 | 3 => state14_1371 | 4 => state14_1372 | 5 => state14_1373 | 6 => state14_1374 | _ => state14_1375

def stree14RLRRLRL (i : Nat) : State := if i < 7 then stree14RLRRLRLL i else stree14RLRRLRLR (i - 7)

def stree14RLRRLRRL (i : Nat) : State := match i with | 0 => state14_1376 | 1 => state14_1377 | 2 => state14_1378 | 3 => state14_1379 | 4 => state14_1380 | 5 => state14_1381 | _ => state14_1382

def stree14RLRRLRRR (i : Nat) : State := match i with | 0 => state14_1383 | 1 => state14_1384 | 2 => state14_1385 | 3 => state14_1386 | 4 => state14_1387 | 5 => state14_1388 | 6 => state14_1389 | _ => state14_1390

def stree14RLRRLRR (i : Nat) : State := if i < 7 then stree14RLRRLRRL i else stree14RLRRLRRR (i - 7)

def stree14RLRRLR (i : Nat) : State := if i < 15 then stree14RLRRLRL i else stree14RLRRLRR (i - 15)

def stree14RLRRL (i : Nat) : State := if i < 30 then stree14RLRRLL i else stree14RLRRLR (i - 30)

def stree14RLRRRLLL (i : Nat) : State := match i with | 0 => state14_1391 | 1 => state14_1392 | 2 => state14_1393 | 3 => state14_1394 | 4 => state14_1395 | 5 => state14_1396 | _ => state14_1397

def stree14RLRRRLLR (i : Nat) : State := match i with | 0 => state14_1398 | 1 => state14_1399 | 2 => state14_1400 | 3 => state14_1401 | 4 => state14_1402 | 5 => state14_1403 | 6 => state14_1404 | _ => state14_1405

def stree14RLRRRLL (i : Nat) : State := if i < 7 then stree14RLRRRLLL i else stree14RLRRRLLR (i - 7)

def stree14RLRRRLRL (i : Nat) : State := match i with | 0 => state14_1406 | 1 => state14_1407 | 2 => state14_1408 | 3 => state14_1409 | 4 => state14_1410 | 5 => state14_1411 | _ => state14_1412

def stree14RLRRRLRR (i : Nat) : State := match i with | 0 => state14_1413 | 1 => state14_1414 | 2 => state14_1415 | 3 => state14_1416 | 4 => state14_1417 | 5 => state14_1418 | 6 => state14_1419 | _ => state14_1420

def stree14RLRRRLR (i : Nat) : State := if i < 7 then stree14RLRRRLRL i else stree14RLRRRLRR (i - 7)

def stree14RLRRRL (i : Nat) : State := if i < 15 then stree14RLRRRLL i else stree14RLRRRLR (i - 15)

def stree14RLRRRRLL (i : Nat) : State := match i with | 0 => state14_1421 | 1 => state14_1422 | 2 => state14_1423 | 3 => state14_1424 | 4 => state14_1425 | 5 => state14_1426 | _ => state14_1427

def stree14RLRRRRLR (i : Nat) : State := match i with | 0 => state14_1428 | 1 => state14_1429 | 2 => state14_1430 | 3 => state14_1431 | 4 => state14_1432 | 5 => state14_1433 | 6 => state14_1434 | _ => state14_1435

def stree14RLRRRRL (i : Nat) : State := if i < 7 then stree14RLRRRRLL i else stree14RLRRRRLR (i - 7)

def stree14RLRRRRRL (i : Nat) : State := match i with | 0 => state14_1436 | 1 => state14_1437 | 2 => state14_1438 | 3 => state14_1439 | 4 => state14_1440 | 5 => state14_1441 | 6 => state14_1442 | _ => state14_1443

def stree14RLRRRRRR (i : Nat) : State := match i with | 0 => state14_1444 | 1 => state14_1445 | 2 => state14_1446 | 3 => state14_1447 | 4 => state14_1448 | 5 => state14_1449 | 6 => state14_1450 | _ => state14_1451

def stree14RLRRRRR (i : Nat) : State := if i < 8 then stree14RLRRRRRL i else stree14RLRRRRRR (i - 8)

def stree14RLRRRR (i : Nat) : State := if i < 15 then stree14RLRRRRL i else stree14RLRRRRR (i - 15)

def stree14RLRRR (i : Nat) : State := if i < 30 then stree14RLRRRL i else stree14RLRRRR (i - 30)

def stree14RLRR (i : Nat) : State := if i < 60 then stree14RLRRL i else stree14RLRRR (i - 60)

def stree14RLR (i : Nat) : State := if i < 121 then stree14RLRL i else stree14RLRR (i - 121)

def stree14RL (i : Nat) : State := if i < 242 then stree14RLL i else stree14RLR (i - 242)

def stree14RRLLLLLL (i : Nat) : State := match i with | 0 => state14_1452 | 1 => state14_1453 | 2 => state14_1454 | 3 => state14_1455 | 4 => state14_1456 | 5 => state14_1457 | _ => state14_1458

def stree14RRLLLLLR (i : Nat) : State := match i with | 0 => state14_1459 | 1 => state14_1460 | 2 => state14_1461 | 3 => state14_1462 | 4 => state14_1463 | 5 => state14_1464 | 6 => state14_1465 | _ => state14_1466

def stree14RRLLLLL (i : Nat) : State := if i < 7 then stree14RRLLLLLL i else stree14RRLLLLLR (i - 7)

def stree14RRLLLLRL (i : Nat) : State := match i with | 0 => state14_1467 | 1 => state14_1468 | 2 => state14_1469 | 3 => state14_1470 | 4 => state14_1471 | 5 => state14_1472 | _ => state14_1473

def stree14RRLLLLRR (i : Nat) : State := match i with | 0 => state14_1474 | 1 => state14_1475 | 2 => state14_1476 | 3 => state14_1477 | 4 => state14_1478 | 5 => state14_1479 | 6 => state14_1480 | _ => state14_1481

def stree14RRLLLLR (i : Nat) : State := if i < 7 then stree14RRLLLLRL i else stree14RRLLLLRR (i - 7)

def stree14RRLLLL (i : Nat) : State := if i < 15 then stree14RRLLLLL i else stree14RRLLLLR (i - 15)

def stree14RRLLLRLL (i : Nat) : State := match i with | 0 => state14_1482 | 1 => state14_1483 | 2 => state14_1484 | 3 => state14_1485 | 4 => state14_1486 | 5 => state14_1487 | _ => state14_1488

def stree14RRLLLRLR (i : Nat) : State := match i with | 0 => state14_1489 | 1 => state14_1490 | 2 => state14_1491 | 3 => state14_1492 | 4 => state14_1493 | 5 => state14_1494 | 6 => state14_1495 | _ => state14_1496

def stree14RRLLLRL (i : Nat) : State := if i < 7 then stree14RRLLLRLL i else stree14RRLLLRLR (i - 7)

def stree14RRLLLRRL (i : Nat) : State := match i with | 0 => state14_1497 | 1 => state14_1498 | 2 => state14_1499 | 3 => state14_1500 | 4 => state14_1501 | 5 => state14_1502 | _ => state14_1503

def stree14RRLLLRRR (i : Nat) : State := match i with | 0 => state14_1504 | 1 => state14_1505 | 2 => state14_1506 | 3 => state14_1507 | 4 => state14_1508 | 5 => state14_1509 | 6 => state14_1510 | _ => state14_1511

def stree14RRLLLRR (i : Nat) : State := if i < 7 then stree14RRLLLRRL i else stree14RRLLLRRR (i - 7)

def stree14RRLLLR (i : Nat) : State := if i < 15 then stree14RRLLLRL i else stree14RRLLLRR (i - 15)

def stree14RRLLL (i : Nat) : State := if i < 30 then stree14RRLLLL i else stree14RRLLLR (i - 30)

def stree14RRLLRLLL (i : Nat) : State := match i with | 0 => state14_1512 | 1 => state14_1513 | 2 => state14_1514 | 3 => state14_1515 | 4 => state14_1516 | 5 => state14_1517 | _ => state14_1518

def stree14RRLLRLLR (i : Nat) : State := match i with | 0 => state14_1519 | 1 => state14_1520 | 2 => state14_1521 | 3 => state14_1522 | 4 => state14_1523 | 5 => state14_1524 | 6 => state14_1525 | _ => state14_1526

def stree14RRLLRLL (i : Nat) : State := if i < 7 then stree14RRLLRLLL i else stree14RRLLRLLR (i - 7)

def stree14RRLLRLRL (i : Nat) : State := match i with | 0 => state14_1527 | 1 => state14_1528 | 2 => state14_1529 | 3 => state14_1530 | 4 => state14_1531 | 5 => state14_1532 | _ => state14_1533

def stree14RRLLRLRR (i : Nat) : State := match i with | 0 => state14_1534 | 1 => state14_1535 | 2 => state14_1536 | 3 => state14_1537 | 4 => state14_1538 | 5 => state14_1539 | 6 => state14_1540 | _ => state14_1541

def stree14RRLLRLR (i : Nat) : State := if i < 7 then stree14RRLLRLRL i else stree14RRLLRLRR (i - 7)

def stree14RRLLRL (i : Nat) : State := if i < 15 then stree14RRLLRLL i else stree14RRLLRLR (i - 15)

def stree14RRLLRRLL (i : Nat) : State := match i with | 0 => state14_1542 | 1 => state14_1543 | 2 => state14_1544 | 3 => state14_1545 | 4 => state14_1546 | 5 => state14_1547 | _ => state14_1548

def stree14RRLLRRLR (i : Nat) : State := match i with | 0 => state14_1549 | 1 => state14_1550 | 2 => state14_1551 | 3 => state14_1552 | 4 => state14_1553 | 5 => state14_1554 | 6 => state14_1555 | _ => state14_1556

def stree14RRLLRRL (i : Nat) : State := if i < 7 then stree14RRLLRRLL i else stree14RRLLRRLR (i - 7)

def stree14RRLLRRRL (i : Nat) : State := match i with | 0 => state14_1557 | 1 => state14_1558 | 2 => state14_1559 | 3 => state14_1560 | 4 => state14_1561 | 5 => state14_1562 | 6 => state14_1563 | _ => state14_1564

def stree14RRLLRRRR (i : Nat) : State := match i with | 0 => state14_1565 | 1 => state14_1566 | 2 => state14_1567 | 3 => state14_1568 | 4 => state14_1569 | 5 => state14_1570 | 6 => state14_1571 | _ => state14_1572

def stree14RRLLRRR (i : Nat) : State := if i < 8 then stree14RRLLRRRL i else stree14RRLLRRRR (i - 8)

def stree14RRLLRR (i : Nat) : State := if i < 15 then stree14RRLLRRL i else stree14RRLLRRR (i - 15)

def stree14RRLLR (i : Nat) : State := if i < 30 then stree14RRLLRL i else stree14RRLLRR (i - 30)

def stree14RRLL (i : Nat) : State := if i < 60 then stree14RRLLL i else stree14RRLLR (i - 60)

def stree14RRLRLLLL (i : Nat) : State := match i with | 0 => state14_1573 | 1 => state14_1574 | 2 => state14_1575 | 3 => state14_1576 | 4 => state14_1577 | 5 => state14_1578 | _ => state14_1579

def stree14RRLRLLLR (i : Nat) : State := match i with | 0 => state14_1580 | 1 => state14_1581 | 2 => state14_1582 | 3 => state14_1583 | 4 => state14_1584 | 5 => state14_1585 | 6 => state14_1586 | _ => state14_1587

def stree14RRLRLLL (i : Nat) : State := if i < 7 then stree14RRLRLLLL i else stree14RRLRLLLR (i - 7)

def stree14RRLRLLRL (i : Nat) : State := match i with | 0 => state14_1588 | 1 => state14_1589 | 2 => state14_1590 | 3 => state14_1591 | 4 => state14_1592 | 5 => state14_1593 | _ => state14_1594

def stree14RRLRLLRR (i : Nat) : State := match i with | 0 => state14_1595 | 1 => state14_1596 | 2 => state14_1597 | 3 => state14_1598 | 4 => state14_1599 | 5 => state14_1600 | 6 => state14_1601 | _ => state14_1602

def stree14RRLRLLR (i : Nat) : State := if i < 7 then stree14RRLRLLRL i else stree14RRLRLLRR (i - 7)

def stree14RRLRLL (i : Nat) : State := if i < 15 then stree14RRLRLLL i else stree14RRLRLLR (i - 15)

def stree14RRLRLRLL (i : Nat) : State := match i with | 0 => state14_1603 | 1 => state14_1604 | 2 => state14_1605 | 3 => state14_1606 | 4 => state14_1607 | 5 => state14_1608 | _ => state14_1609

def stree14RRLRLRLR (i : Nat) : State := match i with | 0 => state14_1610 | 1 => state14_1611 | 2 => state14_1612 | 3 => state14_1613 | 4 => state14_1614 | 5 => state14_1615 | 6 => state14_1616 | _ => state14_1617

def stree14RRLRLRL (i : Nat) : State := if i < 7 then stree14RRLRLRLL i else stree14RRLRLRLR (i - 7)

def stree14RRLRLRRL (i : Nat) : State := match i with | 0 => state14_1618 | 1 => state14_1619 | 2 => state14_1620 | 3 => state14_1621 | 4 => state14_1622 | 5 => state14_1623 | _ => state14_1624

def stree14RRLRLRRR (i : Nat) : State := match i with | 0 => state14_1625 | 1 => state14_1626 | 2 => state14_1627 | 3 => state14_1628 | 4 => state14_1629 | 5 => state14_1630 | 6 => state14_1631 | _ => state14_1632

def stree14RRLRLRR (i : Nat) : State := if i < 7 then stree14RRLRLRRL i else stree14RRLRLRRR (i - 7)

def stree14RRLRLR (i : Nat) : State := if i < 15 then stree14RRLRLRL i else stree14RRLRLRR (i - 15)

def stree14RRLRL (i : Nat) : State := if i < 30 then stree14RRLRLL i else stree14RRLRLR (i - 30)

def stree14RRLRRLLL (i : Nat) : State := match i with | 0 => state14_1633 | 1 => state14_1634 | 2 => state14_1635 | 3 => state14_1636 | 4 => state14_1637 | 5 => state14_1638 | _ => state14_1639

def stree14RRLRRLLR (i : Nat) : State := match i with | 0 => state14_1640 | 1 => state14_1641 | 2 => state14_1642 | 3 => state14_1643 | 4 => state14_1644 | 5 => state14_1645 | 6 => state14_1646 | _ => state14_1647

def stree14RRLRRLL (i : Nat) : State := if i < 7 then stree14RRLRRLLL i else stree14RRLRRLLR (i - 7)

def stree14RRLRRLRL (i : Nat) : State := match i with | 0 => state14_1648 | 1 => state14_1649 | 2 => state14_1650 | 3 => state14_1651 | 4 => state14_1652 | 5 => state14_1653 | _ => state14_1654

def stree14RRLRRLRR (i : Nat) : State := match i with | 0 => state14_1655 | 1 => state14_1656 | 2 => state14_1657 | 3 => state14_1658 | 4 => state14_1659 | 5 => state14_1660 | 6 => state14_1661 | _ => state14_1662

def stree14RRLRRLR (i : Nat) : State := if i < 7 then stree14RRLRRLRL i else stree14RRLRRLRR (i - 7)

def stree14RRLRRL (i : Nat) : State := if i < 15 then stree14RRLRRLL i else stree14RRLRRLR (i - 15)

def stree14RRLRRRLL (i : Nat) : State := match i with | 0 => state14_1663 | 1 => state14_1664 | 2 => state14_1665 | 3 => state14_1666 | 4 => state14_1667 | 5 => state14_1668 | _ => state14_1669

def stree14RRLRRRLR (i : Nat) : State := match i with | 0 => state14_1670 | 1 => state14_1671 | 2 => state14_1672 | 3 => state14_1673 | 4 => state14_1674 | 5 => state14_1675 | 6 => state14_1676 | _ => state14_1677

def stree14RRLRRRL (i : Nat) : State := if i < 7 then stree14RRLRRRLL i else stree14RRLRRRLR (i - 7)

def stree14RRLRRRRL (i : Nat) : State := match i with | 0 => state14_1678 | 1 => state14_1679 | 2 => state14_1680 | 3 => state14_1681 | 4 => state14_1682 | 5 => state14_1683 | 6 => state14_1684 | _ => state14_1685

def stree14RRLRRRRR (i : Nat) : State := match i with | 0 => state14_1686 | 1 => state14_1687 | 2 => state14_1688 | 3 => state14_1689 | 4 => state14_1690 | 5 => state14_1691 | 6 => state14_1692 | _ => state14_1693

def stree14RRLRRRR (i : Nat) : State := if i < 8 then stree14RRLRRRRL i else stree14RRLRRRRR (i - 8)

def stree14RRLRRR (i : Nat) : State := if i < 15 then stree14RRLRRRL i else stree14RRLRRRR (i - 15)

def stree14RRLRR (i : Nat) : State := if i < 30 then stree14RRLRRL i else stree14RRLRRR (i - 30)

def stree14RRLR (i : Nat) : State := if i < 60 then stree14RRLRL i else stree14RRLRR (i - 60)

def stree14RRL (i : Nat) : State := if i < 121 then stree14RRLL i else stree14RRLR (i - 121)

def stree14RRRLLLLL (i : Nat) : State := match i with | 0 => state14_1694 | 1 => state14_1695 | 2 => state14_1696 | 3 => state14_1697 | 4 => state14_1698 | 5 => state14_1699 | _ => state14_1700

def stree14RRRLLLLR (i : Nat) : State := match i with | 0 => state14_1701 | 1 => state14_1702 | 2 => state14_1703 | 3 => state14_1704 | 4 => state14_1705 | 5 => state14_1706 | 6 => state14_1707 | _ => state14_1708

def stree14RRRLLLL (i : Nat) : State := if i < 7 then stree14RRRLLLLL i else stree14RRRLLLLR (i - 7)

def stree14RRRLLLRL (i : Nat) : State := match i with | 0 => state14_1709 | 1 => state14_1710 | 2 => state14_1711 | 3 => state14_1712 | 4 => state14_1713 | 5 => state14_1714 | _ => state14_1715

def stree14RRRLLLRR (i : Nat) : State := match i with | 0 => state14_1716 | 1 => state14_1717 | 2 => state14_1718 | 3 => state14_1719 | 4 => state14_1720 | 5 => state14_1721 | 6 => state14_1722 | _ => state14_1723

def stree14RRRLLLR (i : Nat) : State := if i < 7 then stree14RRRLLLRL i else stree14RRRLLLRR (i - 7)

def stree14RRRLLL (i : Nat) : State := if i < 15 then stree14RRRLLLL i else stree14RRRLLLR (i - 15)

def stree14RRRLLRLL (i : Nat) : State := match i with | 0 => state14_1724 | 1 => state14_1725 | 2 => state14_1726 | 3 => state14_1727 | 4 => state14_1728 | 5 => state14_1729 | _ => state14_1730

def stree14RRRLLRLR (i : Nat) : State := match i with | 0 => state14_1731 | 1 => state14_1732 | 2 => state14_1733 | 3 => state14_1734 | 4 => state14_1735 | 5 => state14_1736 | 6 => state14_1737 | _ => state14_1738

def stree14RRRLLRL (i : Nat) : State := if i < 7 then stree14RRRLLRLL i else stree14RRRLLRLR (i - 7)

def stree14RRRLLRRL (i : Nat) : State := match i with | 0 => state14_1739 | 1 => state14_1740 | 2 => state14_1741 | 3 => state14_1742 | 4 => state14_1743 | 5 => state14_1744 | _ => state14_1745

def stree14RRRLLRRR (i : Nat) : State := match i with | 0 => state14_1746 | 1 => state14_1747 | 2 => state14_1748 | 3 => state14_1749 | 4 => state14_1750 | 5 => state14_1751 | 6 => state14_1752 | _ => state14_1753

def stree14RRRLLRR (i : Nat) : State := if i < 7 then stree14RRRLLRRL i else stree14RRRLLRRR (i - 7)

def stree14RRRLLR (i : Nat) : State := if i < 15 then stree14RRRLLRL i else stree14RRRLLRR (i - 15)

def stree14RRRLL (i : Nat) : State := if i < 30 then stree14RRRLLL i else stree14RRRLLR (i - 30)

def stree14RRRLRLLL (i : Nat) : State := match i with | 0 => state14_1754 | 1 => state14_1755 | 2 => state14_1756 | 3 => state14_1757 | 4 => state14_1758 | 5 => state14_1759 | _ => state14_1760

def stree14RRRLRLLR (i : Nat) : State := match i with | 0 => state14_1761 | 1 => state14_1762 | 2 => state14_1763 | 3 => state14_1764 | 4 => state14_1765 | 5 => state14_1766 | 6 => state14_1767 | _ => state14_1768

def stree14RRRLRLL (i : Nat) : State := if i < 7 then stree14RRRLRLLL i else stree14RRRLRLLR (i - 7)

def stree14RRRLRLRL (i : Nat) : State := match i with | 0 => state14_1769 | 1 => state14_1770 | 2 => state14_1771 | 3 => state14_1772 | 4 => state14_1773 | 5 => state14_1774 | _ => state14_1775

def stree14RRRLRLRR (i : Nat) : State := match i with | 0 => state14_1776 | 1 => state14_1777 | 2 => state14_1778 | 3 => state14_1779 | 4 => state14_1780 | 5 => state14_1781 | 6 => state14_1782 | _ => state14_1783

def stree14RRRLRLR (i : Nat) : State := if i < 7 then stree14RRRLRLRL i else stree14RRRLRLRR (i - 7)

def stree14RRRLRL (i : Nat) : State := if i < 15 then stree14RRRLRLL i else stree14RRRLRLR (i - 15)

def stree14RRRLRRLL (i : Nat) : State := match i with | 0 => state14_1784 | 1 => state14_1785 | 2 => state14_1786 | 3 => state14_1787 | 4 => state14_1788 | 5 => state14_1789 | _ => state14_1790

def stree14RRRLRRLR (i : Nat) : State := match i with | 0 => state14_1791 | 1 => state14_1792 | 2 => state14_1793 | 3 => state14_1794 | 4 => state14_1795 | 5 => state14_1796 | 6 => state14_1797 | _ => state14_1798

def stree14RRRLRRL (i : Nat) : State := if i < 7 then stree14RRRLRRLL i else stree14RRRLRRLR (i - 7)

def stree14RRRLRRRL (i : Nat) : State := match i with | 0 => state14_1799 | 1 => state14_1800 | 2 => state14_1801 | 3 => state14_1802 | 4 => state14_1803 | 5 => state14_1804 | 6 => state14_1805 | _ => state14_1806

def stree14RRRLRRRR (i : Nat) : State := match i with | 0 => state14_1807 | 1 => state14_1808 | 2 => state14_1809 | 3 => state14_1810 | 4 => state14_1811 | 5 => state14_1812 | 6 => state14_1813 | _ => state14_1814

def stree14RRRLRRR (i : Nat) : State := if i < 8 then stree14RRRLRRRL i else stree14RRRLRRRR (i - 8)

def stree14RRRLRR (i : Nat) : State := if i < 15 then stree14RRRLRRL i else stree14RRRLRRR (i - 15)

def stree14RRRLR (i : Nat) : State := if i < 30 then stree14RRRLRL i else stree14RRRLRR (i - 30)

def stree14RRRL (i : Nat) : State := if i < 60 then stree14RRRLL i else stree14RRRLR (i - 60)

def stree14RRRRLLLL (i : Nat) : State := match i with | 0 => state14_1815 | 1 => state14_1816 | 2 => state14_1817 | 3 => state14_1818 | 4 => state14_1819 | 5 => state14_1820 | _ => state14_1821

def stree14RRRRLLLR (i : Nat) : State := match i with | 0 => state14_1822 | 1 => state14_1823 | 2 => state14_1824 | 3 => state14_1825 | 4 => state14_1826 | 5 => state14_1827 | 6 => state14_1828 | _ => state14_1829

def stree14RRRRLLL (i : Nat) : State := if i < 7 then stree14RRRRLLLL i else stree14RRRRLLLR (i - 7)

def stree14RRRRLLRL (i : Nat) : State := match i with | 0 => state14_1830 | 1 => state14_1831 | 2 => state14_1832 | 3 => state14_1833 | 4 => state14_1834 | 5 => state14_1835 | _ => state14_1836

def stree14RRRRLLRR (i : Nat) : State := match i with | 0 => state14_1837 | 1 => state14_1838 | 2 => state14_1839 | 3 => state14_1840 | 4 => state14_1841 | 5 => state14_1842 | 6 => state14_1843 | _ => state14_1844

def stree14RRRRLLR (i : Nat) : State := if i < 7 then stree14RRRRLLRL i else stree14RRRRLLRR (i - 7)

def stree14RRRRLL (i : Nat) : State := if i < 15 then stree14RRRRLLL i else stree14RRRRLLR (i - 15)

def stree14RRRRLRLL (i : Nat) : State := match i with | 0 => state14_1845 | 1 => state14_1846 | 2 => state14_1847 | 3 => state14_1848 | 4 => state14_1849 | 5 => state14_1850 | _ => state14_1851

def stree14RRRRLRLR (i : Nat) : State := match i with | 0 => state14_1852 | 1 => state14_1853 | 2 => state14_1854 | 3 => state14_1855 | 4 => state14_1856 | 5 => state14_1857 | 6 => state14_1858 | _ => state14_1859

def stree14RRRRLRL (i : Nat) : State := if i < 7 then stree14RRRRLRLL i else stree14RRRRLRLR (i - 7)

def stree14RRRRLRRL (i : Nat) : State := match i with | 0 => state14_1860 | 1 => state14_1861 | 2 => state14_1862 | 3 => state14_1863 | 4 => state14_1864 | 5 => state14_1865 | 6 => state14_1866 | _ => state14_1867

def stree14RRRRLRRR (i : Nat) : State := match i with | 0 => state14_1868 | 1 => state14_1869 | 2 => state14_1870 | 3 => state14_1871 | 4 => state14_1872 | 5 => state14_1873 | 6 => state14_1874 | _ => state14_1875

def stree14RRRRLRR (i : Nat) : State := if i < 8 then stree14RRRRLRRL i else stree14RRRRLRRR (i - 8)

def stree14RRRRLR (i : Nat) : State := if i < 15 then stree14RRRRLRL i else stree14RRRRLRR (i - 15)

def stree14RRRRL (i : Nat) : State := if i < 30 then stree14RRRRLL i else stree14RRRRLR (i - 30)

def stree14RRRRRLLL (i : Nat) : State := match i with | 0 => state14_1876 | 1 => state14_1877 | 2 => state14_1878 | 3 => state14_1879 | 4 => state14_1880 | 5 => state14_1881 | _ => state14_1882

def stree14RRRRRLLR (i : Nat) : State := match i with | 0 => state14_1883 | 1 => state14_1884 | 2 => state14_1885 | 3 => state14_1886 | 4 => state14_1887 | 5 => state14_1888 | 6 => state14_1889 | _ => state14_1890

def stree14RRRRRLL (i : Nat) : State := if i < 7 then stree14RRRRRLLL i else stree14RRRRRLLR (i - 7)

def stree14RRRRRLRL (i : Nat) : State := match i with | 0 => state14_1891 | 1 => state14_1892 | 2 => state14_1893 | 3 => state14_1894 | 4 => state14_1895 | 5 => state14_1896 | _ => state14_1897

def stree14RRRRRLRR (i : Nat) : State := match i with | 0 => state14_1898 | 1 => state14_1899 | 2 => state14_1900 | 3 => state14_1901 | 4 => state14_1902 | 5 => state14_1903 | 6 => state14_1904 | _ => state14_1905

def stree14RRRRRLR (i : Nat) : State := if i < 7 then stree14RRRRRLRL i else stree14RRRRRLRR (i - 7)

def stree14RRRRRL (i : Nat) : State := if i < 15 then stree14RRRRRLL i else stree14RRRRRLR (i - 15)

def stree14RRRRRRLL (i : Nat) : State := match i with | 0 => state14_1906 | 1 => state14_1907 | 2 => state14_1908 | 3 => state14_1909 | 4 => state14_1910 | 5 => state14_1911 | _ => state14_1912

def stree14RRRRRRLR (i : Nat) : State := match i with | 0 => state14_1913 | 1 => state14_1914 | 2 => state14_1915 | 3 => state14_1916 | 4 => state14_1917 | 5 => state14_1918 | 6 => state14_1919 | _ => state14_1920

def stree14RRRRRRL (i : Nat) : State := if i < 7 then stree14RRRRRRLL i else stree14RRRRRRLR (i - 7)

def stree14RRRRRRRL (i : Nat) : State := match i with | 0 => state14_1921 | 1 => state14_1922 | 2 => state14_1923 | 3 => state14_1924 | 4 => state14_1925 | 5 => state14_1926 | 6 => state14_1927 | _ => state14_1928

def stree14RRRRRRRR (i : Nat) : State := match i with | 0 => state14_1929 | 1 => state14_1930 | 2 => state14_1931 | 3 => state14_1932 | 4 => state14_1933 | 5 => state14_1934 | 6 => state14_1935 | _ => state14_1936

def stree14RRRRRRR (i : Nat) : State := if i < 8 then stree14RRRRRRRL i else stree14RRRRRRRR (i - 8)

def stree14RRRRRR (i : Nat) : State := if i < 15 then stree14RRRRRRL i else stree14RRRRRRR (i - 15)

def stree14RRRRR (i : Nat) : State := if i < 30 then stree14RRRRRL i else stree14RRRRRR (i - 30)

def stree14RRRR (i : Nat) : State := if i < 61 then stree14RRRRL i else stree14RRRRR (i - 61)

def stree14RRR (i : Nat) : State := if i < 121 then stree14RRRL i else stree14RRRR (i - 121)

def stree14RR (i : Nat) : State := if i < 242 then stree14RRL i else stree14RRR (i - 242)

def stree14R (i : Nat) : State := if i < 484 then stree14RL i else stree14RR (i - 484)

def stree14 (i : Nat) : State := if i < 968 then stree14L i else stree14R (i - 968)

def ntree14LLLLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 4 => ![⟨4,by decide⟩,⟨0,by decide⟩,⟨4,by decide⟩] | 5 => ![⟨4,by decide⟩,⟨1,by decide⟩,⟨5,by decide⟩] | 6 => ![⟨6,by decide⟩,⟨2,by decide⟩,⟨6,by decide⟩] | _ => ![⟨6,by decide⟩,⟨3,by decide⟩,⟨7,by decide⟩]

def ntree14LLLLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 4 => ![⟨12,by decide⟩,⟨8,by decide⟩,⟨12,by decide⟩] | 5 => ![⟨12,by decide⟩,⟨9,by decide⟩,⟨13,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨10,by decide⟩,⟨14,by decide⟩] | _ => ![⟨14,by decide⟩,⟨11,by decide⟩,⟨15,by decide⟩]

def ntree14LLLLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLLLLL i else ntree14LLLLLLLR (i - 8)

def ntree14LLLLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨16,by decide⟩,⟨16,by decide⟩,⟨16,by decide⟩] | 1 => ![⟨16,by decide⟩,⟨17,by decide⟩,⟨17,by decide⟩] | 2 => ![⟨18,by decide⟩,⟨16,by decide⟩,⟨18,by decide⟩] | 3 => ![⟨18,by decide⟩,⟨17,by decide⟩,⟨19,by decide⟩] | 4 => ![⟨20,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨20,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨21,by decide⟩,⟨21,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LLLLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨22,by decide⟩,⟨22,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨23,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨23,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨24,by decide⟩] | 5 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨25,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨26,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨27,by decide⟩]

def ntree14LLLLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLLLRL i else ntree14LLLLLLRR (i - 8)

def ntree14LLLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLLLLL i else ntree14LLLLLLR (i - 16)

def ntree14LLLLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨28,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨29,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨29,by decide⟩,⟨28,by decide⟩,⟨24,by decide⟩] | 3 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨30,by decide⟩,⟨31,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨32,by decide⟩,⟨32,by decide⟩,⟨2,by decide⟩] | 6 => ![⟨32,by decide⟩,⟨33,by decide⟩,⟨3,by decide⟩] | _ => ![⟨34,by decide⟩,⟨30,by decide⟩,⟨4,by decide⟩]

def ntree14LLLLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨34,by decide⟩,⟨31,by decide⟩,⟨5,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨36,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨37,by decide⟩] | 4 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨37,by decide⟩] | 5 => ![⟨38,by decide⟩,⟨38,by decide⟩,⟨38,by decide⟩] | 6 => ![⟨39,by decide⟩,⟨38,by decide⟩,⟨39,by decide⟩] | _ => ![⟨40,by decide⟩,⟨40,by decide⟩,⟨38,by decide⟩]

def ntree14LLLLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLLRLL i else ntree14LLLLLRLR (i - 8)

def ntree14LLLLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨24,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨41,by decide⟩,⟨41,by decide⟩] | 2 => ![⟨42,by decide⟩,⟨0,by decide⟩,⟨42,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨41,by decide⟩,⟨43,by decide⟩] | 4 => ![⟨44,by decide⟩,⟨35,by decide⟩,⟨42,by decide⟩] | 5 => ![⟨45,by decide⟩,⟨0,by decide⟩,⟨45,by decide⟩] | 6 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨8,by decide⟩] | _ => ![⟨47,by decide⟩,⟨47,by decide⟩,⟨0,by decide⟩]

def ntree14LLLLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨48,by decide⟩,⟨46,by decide⟩,⟨12,by decide⟩] | 1 => ![⟨49,by decide⟩,⟨47,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨50,by decide⟩,⟨50,by decide⟩,⟨50,by decide⟩] | _ => ![⟨50,by decide⟩,⟨51,by decide⟩,⟨51,by decide⟩]

def ntree14LLLLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨52,by decide⟩] | 1 => ![⟨53,by decide⟩,⟨53,by decide⟩,⟨50,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨52,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨54,by decide⟩,⟨54,by decide⟩] | _ => ![⟨47,by decide⟩,⟨55,by decide⟩,⟨41,by decide⟩]

def ntree14LLLLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLLLLRRRL i else ntree14LLLLLRRRR (i - 4)

def ntree14LLLLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLLRRL i else ntree14LLLLLRRR (i - 8)

def ntree14LLLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLLLRL i else ntree14LLLLLRR (i - 16)

def ntree14LLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LLLLLL i else ntree14LLLLLR (i - 32)

def ntree14LLLLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨56,by decide⟩,⟨57,by decide⟩,⟨57,by decide⟩] | 2 => ![⟨58,by decide⟩,⟨58,by decide⟩,⟨58,by decide⟩] | 3 => ![⟨58,by decide⟩,⟨59,by decide⟩,⟨59,by decide⟩] | 4 => ![⟨60,by decide⟩,⟨60,by decide⟩,⟨60,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨61,by decide⟩,⟨61,by decide⟩] | 6 => ![⟨2,by decide⟩,⟨62,by decide⟩,⟨62,by decide⟩] | _ => ![⟨63,by decide⟩,⟨63,by decide⟩,⟨0,by decide⟩]

def ntree14LLLLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨64,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨66,by decide⟩,⟨61,by decide⟩] | 3 => ![⟨67,by decide⟩,⟨67,by decide⟩,⟨16,by decide⟩] | 4 => ![⟨68,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨69,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨70,by decide⟩,⟨0,by decide⟩] | _ => ![⟨71,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree14LLLLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLRLLL i else ntree14LLLLRLLR (i - 8)

def ntree14LLLLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨72,by decide⟩,⟨72,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨73,by decide⟩,⟨57,by decide⟩] | 2 => ![⟨74,by decide⟩,⟨74,by decide⟩,⟨58,by decide⟩] | 3 => ![⟨74,by decide⟩,⟨75,by decide⟩,⟨59,by decide⟩] | 4 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨56,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨77,by decide⟩,⟨57,by decide⟩] | 6 => ![⟨30,by decide⟩,⟨78,by decide⟩,⟨61,by decide⟩] | _ => ![⟨32,by decide⟩,⟨79,by decide⟩,⟨62,by decide⟩]

def ntree14LLLLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨80,by decide⟩] | 1 => ![⟨81,by decide⟩,⟨0,by decide⟩,⟨81,by decide⟩] | 2 => ![⟨82,by decide⟩,⟨82,by decide⟩,⟨60,by decide⟩] | 3 => ![⟨83,by decide⟩,⟨83,by decide⟩,⟨56,by decide⟩] | 4 => ![⟨84,by decide⟩,⟨0,by decide⟩,⟨84,by decide⟩] | 5 => ![⟨84,by decide⟩,⟨1,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨86,by decide⟩,⟨86,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨87,by decide⟩]

def ntree14LLLLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLRLRL i else ntree14LLLLRLRR (i - 8)

def ntree14LLLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLLRLL i else ntree14LLLLRLR (i - 16)

def ntree14LLLLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨88,by decide⟩,⟨8,by decide⟩,⟨88,by decide⟩] | 1 => ![⟨89,by decide⟩,⟨56,by decide⟩,⟨89,by decide⟩] | 2 => ![⟨90,by decide⟩,⟨0,by decide⟩,⟨90,by decide⟩] | 3 => ![⟨91,by decide⟩,⟨60,by decide⟩,⟨91,by decide⟩] | 4 => ![⟨92,by decide⟩,⟨8,by decide⟩,⟨92,by decide⟩] | 5 => ![⟨93,by decide⟩,⟨63,by decide⟩,⟨90,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨94,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨95,by decide⟩,⟨0,by decide⟩]

def ntree14LLLLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨56,by decide⟩,⟨96,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨98,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨99,by decide⟩,⟨72,by decide⟩,⟨89,by decide⟩] | 4 => ![⟨100,by decide⟩,⟨30,by decide⟩,⟨90,by decide⟩] | 5 => ![⟨101,by decide⟩,⟨0,by decide⟩,⟨101,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨102,by decide⟩,⟨102,by decide⟩] | _ => ![⟨4,by decide⟩,⟨102,by decide⟩,⟨103,by decide⟩]

def ntree14LLLLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLRRLL i else ntree14LLLLRRLR (i - 8)

def ntree14LLLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨104,by decide⟩,⟨104,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨105,by decide⟩,⟨105,by decide⟩] | 2 => ![⟨106,by decide⟩,⟨82,by decide⟩,⟨91,by decide⟩] | 3 => ![⟨107,by decide⟩,⟨83,by decide⟩,⟨89,by decide⟩] | 4 => ![⟨108,by decide⟩,⟨46,by decide⟩,⟨92,by decide⟩] | 5 => ![⟨109,by decide⟩,⟨0,by decide⟩,⟨109,by decide⟩] | 6 => ![⟨109,by decide⟩,⟨1,by decide⟩,⟨110,by decide⟩] | _ => ![⟨111,by decide⟩,⟨8,by decide⟩,⟨111,by decide⟩]

def ntree14LLLLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨111,by decide⟩,⟨9,by decide⟩,⟨112,by decide⟩] | 1 => ![⟨113,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨114,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨115,by decide⟩]

def ntree14LLLLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨116,by decide⟩,⟨1,by decide⟩,⟨117,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | 2 => ![⟨119,by decide⟩,⟨120,by decide⟩,⟨120,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨121,by decide⟩] | _ => ![⟨122,by decide⟩,⟨1,by decide⟩,⟨123,by decide⟩]

def ntree14LLLLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLLLRRRRL i else ntree14LLLLRRRRR (i - 4)

def ntree14LLLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLLRRRL i else ntree14LLLLRRRR (i - 8)

def ntree14LLLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLLRRL i else ntree14LLLLRRR (i - 16)

def ntree14LLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LLLLRL i else ntree14LLLLRR (i - 32)

def ntree14LLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LLLLL i else ntree14LLLLR (i - 65)

def ntree14LLLRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨124,by decide⟩,⟨118,by decide⟩,⟨125,by decide⟩] | 1 => ![⟨126,by decide⟩,⟨120,by decide⟩,⟨127,by decide⟩] | 2 => ![⟨122,by decide⟩,⟨0,by decide⟩,⟨122,by decide⟩] | 3 => ![⟨124,by decide⟩,⟨0,by decide⟩,⟨124,by decide⟩] | 4 => ![⟨119,by decide⟩,⟨119,by decide⟩,⟨119,by decide⟩] | 5 => ![⟨126,by decide⟩,⟨119,by decide⟩,⟨126,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨128,by decide⟩,⟨128,by decide⟩] | _ => ![⟨116,by decide⟩,⟨0,by decide⟩,⟨116,by decide⟩]

def ntree14LLLRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | 1 => ![⟨129,by decide⟩,⟨0,by decide⟩,⟨129,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨130,by decide⟩] | 3 => ![⟨129,by decide⟩,⟨118,by decide⟩,⟨131,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩] | 5 => ![⟨133,by decide⟩,⟨8,by decide⟩,⟨133,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨134,by decide⟩,⟨134,by decide⟩] | _ => ![⟨0,by decide⟩,⟨135,by decide⟩,⟨135,by decide⟩]

def ntree14LLLRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRLLLL i else ntree14LLLRLLLR (i - 8)

def ntree14LLLRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨122,by decide⟩,⟨135,by decide⟩,⟨136,by decide⟩] | 1 => ![⟨133,by decide⟩,⟨134,by decide⟩,⟨137,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨138,by decide⟩,⟨138,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨139,by decide⟩,⟨139,by decide⟩] | 4 => ![⟨140,by decide⟩,⟨141,by decide⟩,⟨141,by decide⟩] | 5 => ![⟨140,by decide⟩,⟨140,by decide⟩,⟨140,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨142,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨143,by decide⟩]

def ntree14LLLRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨145,by decide⟩,⟨145,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨146,by decide⟩,⟨118,by decide⟩] | 3 => ![⟨147,by decide⟩,⟨148,by decide⟩,⟨120,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨149,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨150,by decide⟩,⟨118,by decide⟩] | 6 => ![⟨147,by decide⟩,⟨147,by decide⟩,⟨119,by decide⟩] | _ => ![⟨30,by decide⟩,⟨151,by decide⟩,⟨128,by decide⟩]

def ntree14LLLRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRLLRL i else ntree14LLLRLLRR (i - 8)

def ntree14LLLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLRLLL i else ntree14LLLRLLR (i - 16)

def ntree14LLLRLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨152,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨153,by decide⟩,⟨154,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨153,by decide⟩,⟨153,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨38,by decide⟩,⟨155,by decide⟩,⟨155,by decide⟩] | 4 => ![⟨156,by decide⟩,⟨30,by decide⟩,⟨129,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨157,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LLLRLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨158,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨115,by decide⟩] | 2 => ![⟨159,by decide⟩,⟨31,by decide⟩,⟨117,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨121,by decide⟩] | 4 => ![⟨160,by decide⟩,⟨1,by decide⟩,⟨123,by decide⟩] | 5 => ![⟨161,by decide⟩,⟨30,by decide⟩,⟨122,by decide⟩] | 6 => ![⟨122,by decide⟩,⟨0,by decide⟩,⟨122,by decide⟩] | _ => ![⟨162,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LLLRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRLRLL i else ntree14LLLRLRLR (i - 8)

def ntree14LLLRLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨158,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨159,by decide⟩,⟨30,by decide⟩,⟨116,by decide⟩] | 2 => ![⟨158,by decide⟩,⟨0,by decide⟩,⟨121,by decide⟩] | 3 => ![⟨160,by decide⟩,⟨0,by decide⟩,⟨122,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨46,by decide⟩,⟨133,by decide⟩] | 5 => ![⟨164,by decide⟩,⟨47,by decide⟩,⟨129,by decide⟩] | 6 => ![⟨165,by decide⟩,⟨165,by decide⟩,⟨0,by decide⟩] | _ => ![⟨166,by decide⟩,⟨166,by decide⟩,⟨0,by decide⟩]

def ntree14LLLRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨168,by decide⟩,⟨168,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨169,by decide⟩,⟨169,by decide⟩,⟨0,by decide⟩] | _ => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨170,by decide⟩]

def ntree14LLLRLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨171,by decide⟩,⟨57,by decide⟩,⟨172,by decide⟩] | 1 => ![⟨171,by decide⟩,⟨56,by decide⟩,⟨171,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨173,by decide⟩,⟨174,by decide⟩] | _ => ![⟨56,by decide⟩,⟨175,by decide⟩,⟨175,by decide⟩]

def ntree14LLLRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLLRLRRRL i else ntree14LLLRLRRRR (i - 4)

def ntree14LLLRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRLRRL i else ntree14LLLRLRRR (i - 8)

def ntree14LLLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLRLRL i else ntree14LLLRLRR (i - 16)

def ntree14LLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LLLRLL i else ntree14LLLRLR (i - 32)

def ntree14LLLRRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨63,by decide⟩,⟨63,by decide⟩,⟨121,by decide⟩] | 1 => ![⟨176,by decide⟩,⟨61,by decide⟩,⟨177,by decide⟩] | 2 => ![⟨176,by decide⟩,⟨0,by decide⟩,⟨176,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨70,by decide⟩,⟨122,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨178,by decide⟩,⟨178,by decide⟩] | 5 => ![⟨179,by decide⟩,⟨180,by decide⟩,⟨180,by decide⟩] | 6 => ![⟨56,by decide⟩,⟨181,by decide⟩,⟨181,by decide⟩] | _ => ![⟨182,by decide⟩,⟨183,by decide⟩,⟨183,by decide⟩]

def ntree14LLLRRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨179,by decide⟩] | 1 => ![⟨182,by decide⟩,⟨182,by decide⟩,⟨182,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨184,by decide⟩,⟨184,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨185,by decide⟩,⟨185,by decide⟩] | 4 => ![⟨186,by decide⟩,⟨186,by decide⟩,⟨179,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨187,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨188,by decide⟩,⟨189,by decide⟩,⟨1,by decide⟩] | _ => ![⟨56,by decide⟩,⟨190,by decide⟩,⟨56,by decide⟩]

def ntree14LLLRRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRRLLL i else ntree14LLLRRLLR (i - 8)

def ntree14LLLRRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨30,by decide⟩,⟨191,by decide⟩,⟨173,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨192,by decide⟩,⟨175,by decide⟩] | 2 => ![⟨63,by decide⟩,⟨193,by decide⟩,⟨178,by decide⟩] | 3 => ![⟨194,by decide⟩,⟨179,by decide⟩,⟨194,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨195,by decide⟩,⟨195,by decide⟩] | 5 => ![⟨196,by decide⟩,⟨197,by decide⟩,⟨197,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨198,by decide⟩,⟨198,by decide⟩] | _ => ![⟨199,by decide⟩,⟨200,by decide⟩,⟨200,by decide⟩]

def ntree14LLLRRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨199,by decide⟩,⟨199,by decide⟩,⟨199,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨196,by decide⟩,⟨196,by decide⟩,⟨196,by decide⟩] | 3 => ![⟨202,by decide⟩,⟨202,by decide⟩,⟨196,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨203,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨204,by decide⟩,⟨204,by decide⟩,⟨179,by decide⟩] | 6 => ![⟨205,by decide⟩,⟨205,by decide⟩,⟨199,by decide⟩] | _ => ![⟨206,by decide⟩,⟨72,by decide⟩,⟨171,by decide⟩]

def ntree14LLLRRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRRLRL i else ntree14LLLRRLRR (i - 8)

def ntree14LLLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLRRLL i else ntree14LLLRRLR (i - 16)

def ntree14LLLRRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨207,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 1 => ![⟨84,by decide⟩,⟨178,by decide⟩,⟨208,by decide⟩] | 2 => ![⟨209,by decide⟩,⟨180,by decide⟩,⟨210,by decide⟩] | 3 => ![⟨209,by decide⟩,⟨179,by decide⟩,⟨209,by decide⟩] | 4 => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨211,by decide⟩] | 5 => ![⟨212,by decide⟩,⟨30,by decide⟩,⟨176,by decide⟩] | 6 => ![⟨213,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨214,by decide⟩,⟨196,by decide⟩,⟨214,by decide⟩]

def ntree14LLLRRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨215,by decide⟩,⟨199,by decide⟩,⟨215,by decide⟩] | 1 => ![⟨216,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨217,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨218,by decide⟩,⟨0,by decide⟩,⟨218,by decide⟩] | 4 => ![⟨219,by decide⟩,⟨56,by decide⟩,⟨219,by decide⟩] | 5 => ![⟨218,by decide⟩,⟨118,by decide⟩,⟨220,by decide⟩] | 6 => ![⟨56,by decide⟩,⟨221,by decide⟩,⟨221,by decide⟩] | _ => ![⟨0,by decide⟩,⟨222,by decide⟩,⟨222,by decide⟩]

def ntree14LLLRRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRRRLL i else ntree14LLLRRRLR (i - 8)

def ntree14LLLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨223,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨60,by decide⟩,⟨224,by decide⟩,⟨224,by decide⟩] | 3 => ![⟨56,by decide⟩,⟨225,by decide⟩,⟨225,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨226,by decide⟩,⟨226,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨227,by decide⟩,⟨227,by decide⟩] | 6 => ![⟨218,by decide⟩,⟨28,by decide⟩,⟨218,by decide⟩] | _ => ![⟨165,by decide⟩,⟨228,by decide⟩,⟨118,by decide⟩]

def ntree14LLLRRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨229,by decide⟩,⟨0,by decide⟩,⟨229,by decide⟩] | 1 => ![⟨230,by decide⟩,⟨0,by decide⟩,⟨230,by decide⟩] | 2 => ![⟨231,by decide⟩,⟨0,by decide⟩,⟨231,by decide⟩] | _ => ![⟨232,by decide⟩,⟨179,by decide⟩,⟨232,by decide⟩]

def ntree14LLLRRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨72,by decide⟩,⟨233,by decide⟩,⟨221,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨234,by decide⟩,⟨222,by decide⟩] | 2 => ![⟨188,by decide⟩,⟨188,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨56,by decide⟩,⟨235,by decide⟩,⟨56,by decide⟩] | _ => ![⟨0,by decide⟩,⟨236,by decide⟩,⟨0,by decide⟩]

def ntree14LLLRRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLLRRRRRL i else ntree14LLLRRRRRR (i - 4)

def ntree14LLLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLLRRRRL i else ntree14LLLRRRRR (i - 8)

def ntree14LLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLLRRRL i else ntree14LLLRRRR (i - 16)

def ntree14LLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LLLRRL i else ntree14LLLRRR (i - 32)

def ntree14LLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LLLRL i else ntree14LLLRR (i - 65)

def ntree14LLL (i : Nat) : Fin 3 → Fin 1937 := if i < 130 then ntree14LLLL i else ntree14LLLR (i - 130)

def ntree14LLRLLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨179,by decide⟩,⟨237,by decide⟩,⟨237,by decide⟩] | 1 => ![⟨238,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨238,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | 3 => ![⟨239,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨240,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 5 => ![⟨241,by decide⟩,⟨30,by decide⟩,⟨218,by decide⟩] | 6 => ![⟨242,by decide⟩,⟨72,by decide⟩,⟨219,by decide⟩] | _ => ![⟨243,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree14LLRLLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨244,by decide⟩,⟨196,by decide⟩,⟨244,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨245,by decide⟩,⟨245,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨246,by decide⟩,⟨246,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨245,by decide⟩,⟨247,by decide⟩] | 4 => ![⟨6,by decide⟩,⟨246,by decide⟩,⟨248,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨249,by decide⟩] | 6 => ![⟨4,by decide⟩,⟨118,by decide⟩,⟨250,by decide⟩] | _ => ![⟨122,by decide⟩,⟨251,by decide⟩,⟨252,by decide⟩]

def ntree14LLRLLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLLLLL i else ntree14LLRLLLLR (i - 8)

def ntree14LLRLLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨251,by decide⟩,⟨251,by decide⟩] | 1 => ![⟨253,by decide⟩,⟨254,by decide⟩,⟨253,by decide⟩] | 2 => ![⟨253,by decide⟩,⟨255,by decide⟩,⟨256,by decide⟩] | 3 => ![⟨254,by decide⟩,⟨254,by decide⟩,⟨254,by decide⟩] | 4 => ![⟨254,by decide⟩,⟨255,by decide⟩,⟨255,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨257,by decide⟩] | 6 => ![⟨4,by decide⟩,⟨128,by decide⟩,⟨258,by decide⟩] | _ => ![⟨122,by decide⟩,⟨0,by decide⟩,⟨122,by decide⟩]

def ntree14LLRLLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨259,by decide⟩,⟨0,by decide⟩,⟨259,by decide⟩] | 1 => ![⟨260,by decide⟩,⟨2,by decide⟩,⟨260,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨261,by decide⟩,⟨261,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨262,by decide⟩,⟨262,by decide⟩] | 4 => ![⟨263,by decide⟩,⟨0,by decide⟩,⟨263,by decide⟩] | 5 => ![⟨264,by decide⟩,⟨2,by decide⟩,⟨264,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨265,by decide⟩] | _ => ![⟨122,by decide⟩,⟨261,by decide⟩,⟨266,by decide⟩]

def ntree14LLRLLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLLLRL i else ntree14LLRLLLRR (i - 8)

def ntree14LLRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRLLLL i else ntree14LLRLLLR (i - 16)

def ntree14LLRLLRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨263,by decide⟩,⟨118,by decide⟩,⟨267,by decide⟩] | 1 => ![⟨264,by decide⟩,⟨262,by decide⟩,⟨268,by decide⟩] | 2 => ![⟨269,by decide⟩,⟨0,by decide⟩,⟨269,by decide⟩] | 3 => ![⟨270,by decide⟩,⟨0,by decide⟩,⟨270,by decide⟩] | 4 => ![⟨271,by decide⟩,⟨140,by decide⟩,⟨271,by decide⟩] | 5 => ![⟨272,by decide⟩,⟨0,by decide⟩,⟨272,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨249,by decide⟩]

def ntree14LLRLLRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨4,by decide⟩,⟨149,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨150,by decide⟩,⟨250,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨149,by decide⟩,⟨249,by decide⟩] | 4 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨257,by decide⟩] | 5 => ![⟨34,by decide⟩,⟨151,by decide⟩,⟨258,by decide⟩] | 6 => ![⟨30,by decide⟩,⟨273,by decide⟩,⟨261,by decide⟩] | _ => ![⟨32,by decide⟩,⟨274,by decide⟩,⟨262,by decide⟩]

def ntree14LLRLLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLLRLL i else ntree14LLRLLRLR (i - 8)

def ntree14LLRLLRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨35,by decide⟩,⟨275,by decide⟩,⟨261,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨276,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨277,by decide⟩] | 3 => ![⟨278,by decide⟩,⟨279,by decide⟩,⟨253,by decide⟩] | 4 => ![⟨279,by decide⟩,⟨279,by decide⟩,⟨254,by decide⟩] | 5 => ![⟨280,by decide⟩,⟨281,by decide⟩,⟨4,by decide⟩] | 6 => ![⟨281,by decide⟩,⟨281,by decide⟩,⟨0,by decide⟩] | _ => ![⟨282,by decide⟩,⟨50,by decide⟩,⟨282,by decide⟩]

def ntree14LLRLLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨283,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨284,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨285,by decide⟩,⟨0,by decide⟩]

def ntree14LLRLLRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨286,by decide⟩,⟨286,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨287,by decide⟩,⟨287,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨288,by decide⟩,⟨288,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨289,by decide⟩,⟨289,by decide⟩,⟨2,by decide⟩] | _ => ![⟨56,by decide⟩,⟨56,by decide⟩,⟨290,by decide⟩]

def ntree14LLRLLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLRLLRRRL i else ntree14LLRLLRRRR (i - 4)

def ntree14LLRLLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLLRRL i else ntree14LLRLLRRR (i - 8)

def ntree14LLRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRLLRL i else ntree14LLRLLRR (i - 16)

def ntree14LLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LLRLLL i else ntree14LLRLLR (i - 32)

def ntree14LLRLRLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨291,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨249,by decide⟩] | 3 => ![⟨292,by decide⟩,⟨56,by decide⟩,⟨292,by decide⟩] | 4 => ![⟨293,by decide⟩,⟨58,by decide⟩,⟨293,by decide⟩] | 5 => ![⟨294,by decide⟩,⟨286,by decide⟩,⟨122,by decide⟩] | 6 => ![⟨295,by decide⟩,⟨0,by decide⟩,⟨295,by decide⟩] | _ => ![⟨296,by decide⟩,⟨2,by decide⟩,⟨296,by decide⟩]

def ntree14LLRLRLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨29,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 1 => ![⟨297,by decide⟩,⟨297,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨298,by decide⟩,⟨298,by decide⟩,⟨179,by decide⟩] | 3 => ![⟨299,by decide⟩,⟨299,by decide⟩,⟨299,by decide⟩] | 4 => ![⟨300,by decide⟩,⟨300,by decide⟩,⟨300,by decide⟩] | 5 => ![⟨301,by decide⟩,⟨301,by decide⟩,⟨299,by decide⟩] | 6 => ![⟨302,by decide⟩,⟨302,by decide⟩,⟨300,by decide⟩] | _ => ![⟨179,by decide⟩,⟨179,by decide⟩,⟨303,by decide⟩]

def ntree14LLRLRLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLRLLL i else ntree14LLRLRLLR (i - 8)

def ntree14LLRLRLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨0,by decide⟩,⟨304,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨305,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨299,by decide⟩,⟨306,by decide⟩,⟨306,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨307,by decide⟩,⟨307,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨309,by decide⟩,⟨309,by decide⟩] | 6 => ![⟨179,by decide⟩,⟨310,by decide⟩,⟨310,by decide⟩] | _ => ![⟨311,by decide⟩,⟨311,by decide⟩,⟨0,by decide⟩]

def ntree14LLRLRLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨122,by decide⟩,⟨304,by decide⟩,⟨122,by decide⟩] | 1 => ![⟨89,by decide⟩,⟨221,by decide⟩,⟨312,by decide⟩] | 2 => ![⟨90,by decide⟩,⟨222,by decide⟩,⟨313,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩] | 4 => ![⟨314,by decide⟩,⟨0,by decide⟩,⟨314,by decide⟩] | 5 => ![⟨315,by decide⟩,⟨56,by decide⟩,⟨315,by decide⟩] | 6 => ![⟨316,by decide⟩,⟨0,by decide⟩,⟨316,by decide⟩] | _ => ![⟨317,by decide⟩,⟨179,by decide⟩,⟨317,by decide⟩]

def ntree14LLRLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLRLRL i else ntree14LLRLRLRR (i - 8)

def ntree14LLRLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRLRLL i else ntree14LLRLRLR (i - 16)

def ntree14LLRLRRLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨318,by decide⟩,⟨182,by decide⟩,⟨318,by decide⟩] | 1 => ![⟨319,by decide⟩,⟨179,by decide⟩,⟨319,by decide⟩] | 2 => ![⟨320,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨321,by decide⟩,⟨0,by decide⟩,⟨321,by decide⟩] | 4 => ![⟨322,by decide⟩,⟨2,by decide⟩,⟨322,by decide⟩] | 5 => ![⟨323,by decide⟩,⟨299,by decide⟩,⟨323,by decide⟩] | 6 => ![⟨324,by decide⟩,⟨300,by decide⟩,⟨324,by decide⟩] | _ => ![⟨314,by decide⟩,⟨102,by decide⟩,⟨325,by decide⟩]

def ntree14LLRLRRLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨317,by decide⟩,⟨237,by decide⟩,⟨326,by decide⟩] | 1 => ![⟨179,by decide⟩,⟨327,by decide⟩,⟨327,by decide⟩] | 2 => ![⟨299,by decide⟩,⟨328,by decide⟩,⟨328,by decide⟩] | 3 => ![⟨300,by decide⟩,⟨329,by decide⟩,⟨329,by decide⟩] | 4 => ![⟨330,by decide⟩,⟨311,by decide⟩,⟨4,by decide⟩] | 5 => ![⟨331,by decide⟩,⟨65,by decide⟩,⟨314,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨332,by decide⟩,⟨0,by decide⟩] | _ => ![⟨333,by decide⟩,⟨334,by decide⟩,⟨1,by decide⟩]

def ntree14LLRLRRL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLRRLL i else ntree14LLRLRRLR (i - 8)

def ntree14LLRLRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨4,by decide⟩,⟨332,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨335,by decide⟩,⟨334,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨336,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨337,by decide⟩,⟨337,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨333,by decide⟩,⟨333,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨338,by decide⟩,⟨338,by decide⟩,⟨0,by decide⟩] | _ => ![⟨339,by decide⟩,⟨337,by decide⟩,⟨12,by decide⟩]

def ntree14LLRLRRRRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨335,by decide⟩,⟨333,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨340,by decide⟩,⟨338,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨341,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | _ => ![⟨336,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree14LLRLRRRRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨342,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨343,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨344,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩] | _ => ![⟨346,by decide⟩,⟨347,by decide⟩,⟨347,by decide⟩]

def ntree14LLRLRRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 4 then ntree14LLRLRRRRL i else ntree14LLRLRRRRR (i - 4)

def ntree14LLRLRRR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRLRRRL i else ntree14LLRLRRRR (i - 8)

def ntree14LLRLRR (i : Nat) : Fin 3 → Fin 1937 := if i < 16 then ntree14LLRLRRL i else ntree14LLRLRRR (i - 16)

def ntree14LLRLR (i : Nat) : Fin 3 → Fin 1937 := if i < 32 then ntree14LLRLRL i else ntree14LLRLRR (i - 32)

def ntree14LLRL (i : Nat) : Fin 3 → Fin 1937 := if i < 65 then ntree14LLRLL i else ntree14LLRLR (i - 65)

def ntree14LLRRLLLL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨4,by decide⟩,⟨345,by decide⟩,⟨348,by decide⟩] | 1 => ![⟨349,by decide⟩,⟨347,by decide⟩,⟨350,by decide⟩] | 2 => ![⟨20,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩] | 3 => ![⟨351,by decide⟩,⟨347,by decide⟩,⟨347,by decide⟩] | 4 => ![⟨336,by decide⟩,⟨345,by decide⟩,⟨345,by decide⟩] | 5 => ![⟨22,by decide⟩,⟨352,by decide⟩,⟨345,by decide⟩] | 6 => ![⟨353,by decide⟩,⟨345,by decide⟩,⟨354,by decide⟩] | _ => ![⟨8,by decide⟩,⟨355,by decide⟩,⟨355,by decide⟩]

def ntree14LLRRLLLR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨333,by decide⟩,⟨333,by decide⟩,⟨24,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | 2 => ![⟨357,by decide⟩,⟨358,by decide⟩,⟨358,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨356,by decide⟩,⟨359,by decide⟩] | 4 => ![⟨360,by decide⟩,⟨358,by decide⟩,⟨361,by decide⟩] | 5 => ![⟨338,by decide⟩,⟨362,by decide⟩,⟨356,by decide⟩] | 6 => ![⟨30,by decide⟩,⟨363,by decide⟩,⟨356,by decide⟩] | _ => ![⟨364,by decide⟩,⟨0,by decide⟩,⟨364,by decide⟩]

def ntree14LLRRLLL (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRLLLL i else ntree14LLRRLLLR (i - 8)

def ntree14LLRRLLRL (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨365,by decide⟩,⟨30,by decide⟩,⟨364,by decide⟩] | 1 => ![⟨20,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨366,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨367,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨368,by decide⟩,⟨366,by decide⟩,⟨24,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨369,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨30,by decide⟩,⟨370,by decide⟩,⟨371,by decide⟩] | _ => ![⟨0,by decide⟩,⟨371,by decide⟩,⟨371,by decide⟩]

def ntree14LLRRLLRR (i : Nat) : Fin 3 → Fin 1937 := match i with | 0 => ![⟨357,by decide⟩,⟨357,by decide⟩,⟨357,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨372,by decide⟩] | 2 => ![⟨357,by decide⟩,⟨357,by decide⟩,⟨373,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨375,by decide⟩,⟨375,by decide⟩] | 5 => ![⟨12,by decide⟩,⟨374,by decide⟩,⟨376,by decide⟩] | 6 => ![⟨4,by decide⟩,⟨375,by decide⟩,⟨377,by decide⟩] | _ => ![⟨46,by decide⟩,⟨378,by decide⟩,⟨374,by decide⟩]

def ntree14LLRRLLR (i : Nat) : Fin 3 → Fin 1937 := if i < 8 then ntree14LLRRLLRL i else ntree14LLRRLLRR (i - 8)

end Paper2.Certificates.Q6.Coverage
