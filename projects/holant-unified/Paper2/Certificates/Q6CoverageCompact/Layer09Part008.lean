import Paper2.Certificates.Q6CoverageCompact.Layer09Part007

namespace Paper2.Certificates.Q6.Coverage

def stree9LLLRLLLLL (i : Nat) : State := match i with | 0 => state9_252 | 1 => state9_253 | 2 => state9_254 | 3 => state9_255 | 4 => state9_256 | 5 => state9_257 | _ => state9_258

def stree9LLLRLLLLR (i : Nat) : State := match i with | 0 => state9_259 | 1 => state9_260 | 2 => state9_261 | 3 => state9_262 | 4 => state9_263 | 5 => state9_264 | 6 => state9_265 | _ => state9_266

def stree9LLLRLLLL (i : Nat) : State := if i < 7 then stree9LLLRLLLLL i else stree9LLLRLLLLR (i - 7)

def stree9LLLRLLLRL (i : Nat) : State := match i with | 0 => state9_267 | 1 => state9_268 | 2 => state9_269 | 3 => state9_270 | 4 => state9_271 | 5 => state9_272 | 6 => state9_273 | _ => state9_274

def stree9LLLRLLLRR (i : Nat) : State := match i with | 0 => state9_275 | 1 => state9_276 | 2 => state9_277 | 3 => state9_278 | 4 => state9_279 | 5 => state9_280 | 6 => state9_281 | _ => state9_282

def stree9LLLRLLLR (i : Nat) : State := if i < 8 then stree9LLLRLLLRL i else stree9LLLRLLLRR (i - 8)

def stree9LLLRLLL (i : Nat) : State := if i < 15 then stree9LLLRLLLL i else stree9LLLRLLLR (i - 15)

def stree9LLLRLLRLL (i : Nat) : State := match i with | 0 => state9_283 | 1 => state9_284 | 2 => state9_285 | 3 => state9_286 | 4 => state9_287 | 5 => state9_288 | 6 => state9_289 | _ => state9_290

def stree9LLLRLLRLR (i : Nat) : State := match i with | 0 => state9_291 | 1 => state9_292 | 2 => state9_293 | 3 => state9_294 | 4 => state9_295 | 5 => state9_296 | 6 => state9_297 | _ => state9_298

def stree9LLLRLLRL (i : Nat) : State := if i < 8 then stree9LLLRLLRLL i else stree9LLLRLLRLR (i - 8)

def stree9LLLRLLRRL (i : Nat) : State := match i with | 0 => state9_299 | 1 => state9_300 | 2 => state9_301 | 3 => state9_302 | 4 => state9_303 | 5 => state9_304 | 6 => state9_305 | _ => state9_306

def stree9LLLRLLRRR (i : Nat) : State := match i with | 0 => state9_307 | 1 => state9_308 | 2 => state9_309 | 3 => state9_310 | 4 => state9_311 | 5 => state9_312 | 6 => state9_313 | _ => state9_314

def stree9LLLRLLRR (i : Nat) : State := if i < 8 then stree9LLLRLLRRL i else stree9LLLRLLRRR (i - 8)

def stree9LLLRLLR (i : Nat) : State := if i < 16 then stree9LLLRLLRL i else stree9LLLRLLRR (i - 16)

def stree9LLLRLL (i : Nat) : State := if i < 31 then stree9LLLRLLL i else stree9LLLRLLR (i - 31)

def stree9LLLRLRLLL (i : Nat) : State := match i with | 0 => state9_315 | 1 => state9_316 | 2 => state9_317 | 3 => state9_318 | 4 => state9_319 | 5 => state9_320 | _ => state9_321

def stree9LLLRLRLLR (i : Nat) : State := match i with | 0 => state9_322 | 1 => state9_323 | 2 => state9_324 | 3 => state9_325 | 4 => state9_326 | 5 => state9_327 | 6 => state9_328 | _ => state9_329

def stree9LLLRLRLL (i : Nat) : State := if i < 7 then stree9LLLRLRLLL i else stree9LLLRLRLLR (i - 7)

def stree9LLLRLRLRL (i : Nat) : State := match i with | 0 => state9_330 | 1 => state9_331 | 2 => state9_332 | 3 => state9_333 | 4 => state9_334 | 5 => state9_335 | 6 => state9_336 | _ => state9_337

def stree9LLLRLRLRR (i : Nat) : State := match i with | 0 => state9_338 | 1 => state9_339 | 2 => state9_340 | 3 => state9_341 | 4 => state9_342 | 5 => state9_343 | 6 => state9_344 | _ => state9_345

def stree9LLLRLRLR (i : Nat) : State := if i < 8 then stree9LLLRLRLRL i else stree9LLLRLRLRR (i - 8)

def stree9LLLRLRL (i : Nat) : State := if i < 15 then stree9LLLRLRLL i else stree9LLLRLRLR (i - 15)

def stree9LLLRLRRLL (i : Nat) : State := match i with | 0 => state9_346 | 1 => state9_347 | 2 => state9_348 | 3 => state9_349 | 4 => state9_350 | 5 => state9_351 | 6 => state9_352 | _ => state9_353

def stree9LLLRLRRLR (i : Nat) : State := match i with | 0 => state9_354 | 1 => state9_355 | 2 => state9_356 | 3 => state9_357 | 4 => state9_358 | 5 => state9_359 | 6 => state9_360 | _ => state9_361

def stree9LLLRLRRL (i : Nat) : State := if i < 8 then stree9LLLRLRRLL i else stree9LLLRLRRLR (i - 8)

def stree9LLLRLRRRL (i : Nat) : State := match i with | 0 => state9_362 | 1 => state9_363 | 2 => state9_364 | 3 => state9_365 | 4 => state9_366 | 5 => state9_367 | 6 => state9_368 | _ => state9_369

def stree9LLLRLRRRR (i : Nat) : State := match i with | 0 => state9_370 | 1 => state9_371 | 2 => state9_372 | 3 => state9_373 | 4 => state9_374 | 5 => state9_375 | 6 => state9_376 | _ => state9_377

def stree9LLLRLRRR (i : Nat) : State := if i < 8 then stree9LLLRLRRRL i else stree9LLLRLRRRR (i - 8)

def stree9LLLRLRR (i : Nat) : State := if i < 16 then stree9LLLRLRRL i else stree9LLLRLRRR (i - 16)

def stree9LLLRLR (i : Nat) : State := if i < 31 then stree9LLLRLRL i else stree9LLLRLRR (i - 31)

def stree9LLLRL (i : Nat) : State := if i < 63 then stree9LLLRLL i else stree9LLLRLR (i - 63)

def stree9LLLRRLLLL (i : Nat) : State := match i with | 0 => state9_378 | 1 => state9_379 | 2 => state9_380 | 3 => state9_381 | 4 => state9_382 | 5 => state9_383 | _ => state9_384

def stree9LLLRRLLLR (i : Nat) : State := match i with | 0 => state9_385 | 1 => state9_386 | 2 => state9_387 | 3 => state9_388 | 4 => state9_389 | 5 => state9_390 | 6 => state9_391 | _ => state9_392

def stree9LLLRRLLL (i : Nat) : State := if i < 7 then stree9LLLRRLLLL i else stree9LLLRRLLLR (i - 7)

def stree9LLLRRLLRL (i : Nat) : State := match i with | 0 => state9_393 | 1 => state9_394 | 2 => state9_395 | 3 => state9_396 | 4 => state9_397 | 5 => state9_398 | 6 => state9_399 | _ => state9_400

def stree9LLLRRLLRR (i : Nat) : State := match i with | 0 => state9_401 | 1 => state9_402 | 2 => state9_403 | 3 => state9_404 | 4 => state9_405 | 5 => state9_406 | 6 => state9_407 | _ => state9_408

def stree9LLLRRLLR (i : Nat) : State := if i < 8 then stree9LLLRRLLRL i else stree9LLLRRLLRR (i - 8)

def stree9LLLRRLL (i : Nat) : State := if i < 15 then stree9LLLRRLLL i else stree9LLLRRLLR (i - 15)

def stree9LLLRRLRLL (i : Nat) : State := match i with | 0 => state9_409 | 1 => state9_410 | 2 => state9_411 | 3 => state9_412 | 4 => state9_413 | 5 => state9_414 | 6 => state9_415 | _ => state9_416

def stree9LLLRRLRLR (i : Nat) : State := match i with | 0 => state9_417 | 1 => state9_418 | 2 => state9_419 | 3 => state9_420 | 4 => state9_421 | 5 => state9_422 | 6 => state9_423 | _ => state9_424

def stree9LLLRRLRL (i : Nat) : State := if i < 8 then stree9LLLRRLRLL i else stree9LLLRRLRLR (i - 8)

def stree9LLLRRLRRL (i : Nat) : State := match i with | 0 => state9_425 | 1 => state9_426 | 2 => state9_427 | 3 => state9_428 | 4 => state9_429 | 5 => state9_430 | 6 => state9_431 | _ => state9_432

def stree9LLLRRLRRR (i : Nat) : State := match i with | 0 => state9_433 | 1 => state9_434 | 2 => state9_435 | 3 => state9_436 | 4 => state9_437 | 5 => state9_438 | 6 => state9_439 | _ => state9_440

def stree9LLLRRLRR (i : Nat) : State := if i < 8 then stree9LLLRRLRRL i else stree9LLLRRLRRR (i - 8)

def stree9LLLRRLR (i : Nat) : State := if i < 16 then stree9LLLRRLRL i else stree9LLLRRLRR (i - 16)

def stree9LLLRRL (i : Nat) : State := if i < 31 then stree9LLLRRLL i else stree9LLLRRLR (i - 31)

def stree9LLLRRRLLL (i : Nat) : State := match i with | 0 => state9_441 | 1 => state9_442 | 2 => state9_443 | 3 => state9_444 | 4 => state9_445 | 5 => state9_446 | _ => state9_447

def stree9LLLRRRLLR (i : Nat) : State := match i with | 0 => state9_448 | 1 => state9_449 | 2 => state9_450 | 3 => state9_451 | 4 => state9_452 | 5 => state9_453 | 6 => state9_454 | _ => state9_455

def stree9LLLRRRLL (i : Nat) : State := if i < 7 then stree9LLLRRRLLL i else stree9LLLRRRLLR (i - 7)

def stree9LLLRRRLRL (i : Nat) : State := match i with | 0 => state9_456 | 1 => state9_457 | 2 => state9_458 | 3 => state9_459 | 4 => state9_460 | 5 => state9_461 | 6 => state9_462 | _ => state9_463

def stree9LLLRRRLRR (i : Nat) : State := match i with | 0 => state9_464 | 1 => state9_465 | 2 => state9_466 | 3 => state9_467 | 4 => state9_468 | 5 => state9_469 | 6 => state9_470 | _ => state9_471

def stree9LLLRRRLR (i : Nat) : State := if i < 8 then stree9LLLRRRLRL i else stree9LLLRRRLRR (i - 8)

def stree9LLLRRRL (i : Nat) : State := if i < 15 then stree9LLLRRRLL i else stree9LLLRRRLR (i - 15)

def stree9LLLRRRRLL (i : Nat) : State := match i with | 0 => state9_472 | 1 => state9_473 | 2 => state9_474 | 3 => state9_475 | 4 => state9_476 | 5 => state9_477 | 6 => state9_478 | _ => state9_479

def stree9LLLRRRRLR (i : Nat) : State := match i with | 0 => state9_480 | 1 => state9_481 | 2 => state9_482 | 3 => state9_483 | 4 => state9_484 | 5 => state9_485 | 6 => state9_486 | _ => state9_487

def stree9LLLRRRRL (i : Nat) : State := if i < 8 then stree9LLLRRRRLL i else stree9LLLRRRRLR (i - 8)

def stree9LLLRRRRRL (i : Nat) : State := match i with | 0 => state9_488 | 1 => state9_489 | 2 => state9_490 | 3 => state9_491 | 4 => state9_492 | 5 => state9_493 | 6 => state9_494 | _ => state9_495

def stree9LLLRRRRRR (i : Nat) : State := match i with | 0 => state9_496 | 1 => state9_497 | 2 => state9_498 | 3 => state9_499 | 4 => state9_500 | 5 => state9_501 | 6 => state9_502 | _ => state9_503

def stree9LLLRRRRR (i : Nat) : State := if i < 8 then stree9LLLRRRRRL i else stree9LLLRRRRRR (i - 8)

def stree9LLLRRRR (i : Nat) : State := if i < 16 then stree9LLLRRRRL i else stree9LLLRRRRR (i - 16)

def stree9LLLRRR (i : Nat) : State := if i < 31 then stree9LLLRRRL i else stree9LLLRRRR (i - 31)

def stree9LLLRR (i : Nat) : State := if i < 63 then stree9LLLRRL i else stree9LLLRRR (i - 63)

def stree9LLLR (i : Nat) : State := if i < 126 then stree9LLLRL i else stree9LLLRR (i - 126)

def stree9LLL (i : Nat) : State := if i < 252 then stree9LLLL i else stree9LLLR (i - 252)

def stree9LLRLLLLLL (i : Nat) : State := match i with | 0 => state9_504 | 1 => state9_505 | 2 => state9_506 | 3 => state9_507 | 4 => state9_508 | 5 => state9_509 | _ => state9_510

def stree9LLRLLLLLR (i : Nat) : State := match i with | 0 => state9_511 | 1 => state9_512 | 2 => state9_513 | 3 => state9_514 | 4 => state9_515 | 5 => state9_516 | 6 => state9_517 | _ => state9_518

def stree9LLRLLLLL (i : Nat) : State := if i < 7 then stree9LLRLLLLLL i else stree9LLRLLLLLR (i - 7)

def stree9LLRLLLLRL (i : Nat) : State := match i with | 0 => state9_519 | 1 => state9_520 | 2 => state9_521 | 3 => state9_522 | 4 => state9_523 | 5 => state9_524 | 6 => state9_525 | _ => state9_526

def stree9LLRLLLLRR (i : Nat) : State := match i with | 0 => state9_527 | 1 => state9_528 | 2 => state9_529 | 3 => state9_530 | 4 => state9_531 | 5 => state9_532 | 6 => state9_533 | _ => state9_534

def stree9LLRLLLLR (i : Nat) : State := if i < 8 then stree9LLRLLLLRL i else stree9LLRLLLLRR (i - 8)

def stree9LLRLLLL (i : Nat) : State := if i < 15 then stree9LLRLLLLL i else stree9LLRLLLLR (i - 15)

def stree9LLRLLLRLL (i : Nat) : State := match i with | 0 => state9_535 | 1 => state9_536 | 2 => state9_537 | 3 => state9_538 | 4 => state9_539 | 5 => state9_540 | 6 => state9_541 | _ => state9_542

def stree9LLRLLLRLR (i : Nat) : State := match i with | 0 => state9_543 | 1 => state9_544 | 2 => state9_545 | 3 => state9_546 | 4 => state9_547 | 5 => state9_548 | 6 => state9_549 | _ => state9_550

def stree9LLRLLLRL (i : Nat) : State := if i < 8 then stree9LLRLLLRLL i else stree9LLRLLLRLR (i - 8)

def stree9LLRLLLRRL (i : Nat) : State := match i with | 0 => state9_551 | 1 => state9_552 | 2 => state9_553 | 3 => state9_554 | 4 => state9_555 | 5 => state9_556 | 6 => state9_557 | _ => state9_558

def stree9LLRLLLRRR (i : Nat) : State := match i with | 0 => state9_559 | 1 => state9_560 | 2 => state9_561 | 3 => state9_562 | 4 => state9_563 | 5 => state9_564 | 6 => state9_565 | _ => state9_566

def stree9LLRLLLRR (i : Nat) : State := if i < 8 then stree9LLRLLLRRL i else stree9LLRLLLRRR (i - 8)

def stree9LLRLLLR (i : Nat) : State := if i < 16 then stree9LLRLLLRL i else stree9LLRLLLRR (i - 16)

def stree9LLRLLL (i : Nat) : State := if i < 31 then stree9LLRLLLL i else stree9LLRLLLR (i - 31)

def stree9LLRLLRLLL (i : Nat) : State := match i with | 0 => state9_567 | 1 => state9_568 | 2 => state9_569 | 3 => state9_570 | 4 => state9_571 | 5 => state9_572 | _ => state9_573

def stree9LLRLLRLLR (i : Nat) : State := match i with | 0 => state9_574 | 1 => state9_575 | 2 => state9_576 | 3 => state9_577 | 4 => state9_578 | 5 => state9_579 | 6 => state9_580 | _ => state9_581

def stree9LLRLLRLL (i : Nat) : State := if i < 7 then stree9LLRLLRLLL i else stree9LLRLLRLLR (i - 7)

def stree9LLRLLRLRL (i : Nat) : State := match i with | 0 => state9_582 | 1 => state9_583 | 2 => state9_584 | 3 => state9_585 | 4 => state9_586 | 5 => state9_587 | 6 => state9_588 | _ => state9_589

def stree9LLRLLRLRR (i : Nat) : State := match i with | 0 => state9_590 | 1 => state9_591 | 2 => state9_592 | 3 => state9_593 | 4 => state9_594 | 5 => state9_595 | 6 => state9_596 | _ => state9_597

def stree9LLRLLRLR (i : Nat) : State := if i < 8 then stree9LLRLLRLRL i else stree9LLRLLRLRR (i - 8)

def stree9LLRLLRL (i : Nat) : State := if i < 15 then stree9LLRLLRLL i else stree9LLRLLRLR (i - 15)

def stree9LLRLLRRLL (i : Nat) : State := match i with | 0 => state9_598 | 1 => state9_599 | 2 => state9_600 | 3 => state9_601 | 4 => state9_602 | 5 => state9_603 | 6 => state9_604 | _ => state9_605

def stree9LLRLLRRLR (i : Nat) : State := match i with | 0 => state9_606 | 1 => state9_607 | 2 => state9_608 | 3 => state9_609 | 4 => state9_610 | 5 => state9_611 | 6 => state9_612 | _ => state9_613

def stree9LLRLLRRL (i : Nat) : State := if i < 8 then stree9LLRLLRRLL i else stree9LLRLLRRLR (i - 8)

def stree9LLRLLRRRL (i : Nat) : State := match i with | 0 => state9_614 | 1 => state9_615 | 2 => state9_616 | 3 => state9_617 | 4 => state9_618 | 5 => state9_619 | 6 => state9_620 | _ => state9_621

def stree9LLRLLRRRR (i : Nat) : State := match i with | 0 => state9_622 | 1 => state9_623 | 2 => state9_624 | 3 => state9_625 | 4 => state9_626 | 5 => state9_627 | 6 => state9_628 | _ => state9_629

def stree9LLRLLRRR (i : Nat) : State := if i < 8 then stree9LLRLLRRRL i else stree9LLRLLRRRR (i - 8)

def stree9LLRLLRR (i : Nat) : State := if i < 16 then stree9LLRLLRRL i else stree9LLRLLRRR (i - 16)

def stree9LLRLLR (i : Nat) : State := if i < 31 then stree9LLRLLRL i else stree9LLRLLRR (i - 31)

def stree9LLRLL (i : Nat) : State := if i < 63 then stree9LLRLLL i else stree9LLRLLR (i - 63)

def stree9LLRLRLLLL (i : Nat) : State := match i with | 0 => state9_630 | 1 => state9_631 | 2 => state9_632 | 3 => state9_633 | 4 => state9_634 | 5 => state9_635 | _ => state9_636

def stree9LLRLRLLLR (i : Nat) : State := match i with | 0 => state9_637 | 1 => state9_638 | 2 => state9_639 | 3 => state9_640 | 4 => state9_641 | 5 => state9_642 | 6 => state9_643 | _ => state9_644

def stree9LLRLRLLL (i : Nat) : State := if i < 7 then stree9LLRLRLLLL i else stree9LLRLRLLLR (i - 7)

def stree9LLRLRLLRL (i : Nat) : State := match i with | 0 => state9_645 | 1 => state9_646 | 2 => state9_647 | 3 => state9_648 | 4 => state9_649 | 5 => state9_650 | 6 => state9_651 | _ => state9_652

def stree9LLRLRLLRR (i : Nat) : State := match i with | 0 => state9_653 | 1 => state9_654 | 2 => state9_655 | 3 => state9_656 | 4 => state9_657 | 5 => state9_658 | 6 => state9_659 | _ => state9_660

def stree9LLRLRLLR (i : Nat) : State := if i < 8 then stree9LLRLRLLRL i else stree9LLRLRLLRR (i - 8)

def stree9LLRLRLL (i : Nat) : State := if i < 15 then stree9LLRLRLLL i else stree9LLRLRLLR (i - 15)

def stree9LLRLRLRLL (i : Nat) : State := match i with | 0 => state9_661 | 1 => state9_662 | 2 => state9_663 | 3 => state9_664 | 4 => state9_665 | 5 => state9_666 | 6 => state9_667 | _ => state9_668

def stree9LLRLRLRLR (i : Nat) : State := match i with | 0 => state9_669 | 1 => state9_670 | 2 => state9_671 | 3 => state9_672 | 4 => state9_673 | 5 => state9_674 | 6 => state9_675 | _ => state9_676

def stree9LLRLRLRL (i : Nat) : State := if i < 8 then stree9LLRLRLRLL i else stree9LLRLRLRLR (i - 8)

def stree9LLRLRLRRL (i : Nat) : State := match i with | 0 => state9_677 | 1 => state9_678 | 2 => state9_679 | 3 => state9_680 | 4 => state9_681 | 5 => state9_682 | 6 => state9_683 | _ => state9_684

def stree9LLRLRLRRR (i : Nat) : State := match i with | 0 => state9_685 | 1 => state9_686 | 2 => state9_687 | 3 => state9_688 | 4 => state9_689 | 5 => state9_690 | 6 => state9_691 | _ => state9_692

def stree9LLRLRLRR (i : Nat) : State := if i < 8 then stree9LLRLRLRRL i else stree9LLRLRLRRR (i - 8)

def stree9LLRLRLR (i : Nat) : State := if i < 16 then stree9LLRLRLRL i else stree9LLRLRLRR (i - 16)

def stree9LLRLRL (i : Nat) : State := if i < 31 then stree9LLRLRLL i else stree9LLRLRLR (i - 31)

def stree9LLRLRRLLL (i : Nat) : State := match i with | 0 => state9_693 | 1 => state9_694 | 2 => state9_695 | 3 => state9_696 | 4 => state9_697 | 5 => state9_698 | _ => state9_699

def stree9LLRLRRLLR (i : Nat) : State := match i with | 0 => state9_700 | 1 => state9_701 | 2 => state9_702 | 3 => state9_703 | 4 => state9_704 | 5 => state9_705 | 6 => state9_706 | _ => state9_707

def stree9LLRLRRLL (i : Nat) : State := if i < 7 then stree9LLRLRRLLL i else stree9LLRLRRLLR (i - 7)

def stree9LLRLRRLRL (i : Nat) : State := match i with | 0 => state9_708 | 1 => state9_709 | 2 => state9_710 | 3 => state9_711 | 4 => state9_712 | 5 => state9_713 | 6 => state9_714 | _ => state9_715

def stree9LLRLRRLRR (i : Nat) : State := match i with | 0 => state9_716 | 1 => state9_717 | 2 => state9_718 | 3 => state9_719 | 4 => state9_720 | 5 => state9_721 | 6 => state9_722 | _ => state9_723

def stree9LLRLRRLR (i : Nat) : State := if i < 8 then stree9LLRLRRLRL i else stree9LLRLRRLRR (i - 8)

def stree9LLRLRRL (i : Nat) : State := if i < 15 then stree9LLRLRRLL i else stree9LLRLRRLR (i - 15)

def stree9LLRLRRRLL (i : Nat) : State := match i with | 0 => state9_724 | 1 => state9_725 | 2 => state9_726 | 3 => state9_727 | 4 => state9_728 | 5 => state9_729 | 6 => state9_730 | _ => state9_731

def stree9LLRLRRRLR (i : Nat) : State := match i with | 0 => state9_732 | 1 => state9_733 | 2 => state9_734 | 3 => state9_735 | 4 => state9_736 | 5 => state9_737 | 6 => state9_738 | _ => state9_739

def stree9LLRLRRRL (i : Nat) : State := if i < 8 then stree9LLRLRRRLL i else stree9LLRLRRRLR (i - 8)

def stree9LLRLRRRRL (i : Nat) : State := match i with | 0 => state9_740 | 1 => state9_741 | 2 => state9_742 | 3 => state9_743 | 4 => state9_744 | 5 => state9_745 | 6 => state9_746 | _ => state9_747

def stree9LLRLRRRRR (i : Nat) : State := match i with | 0 => state9_748 | 1 => state9_749 | 2 => state9_750 | 3 => state9_751 | 4 => state9_752 | 5 => state9_753 | 6 => state9_754 | _ => state9_755

def stree9LLRLRRRR (i : Nat) : State := if i < 8 then stree9LLRLRRRRL i else stree9LLRLRRRRR (i - 8)

def stree9LLRLRRR (i : Nat) : State := if i < 16 then stree9LLRLRRRL i else stree9LLRLRRRR (i - 16)

def stree9LLRLRR (i : Nat) : State := if i < 31 then stree9LLRLRRL i else stree9LLRLRRR (i - 31)

def stree9LLRLR (i : Nat) : State := if i < 63 then stree9LLRLRL i else stree9LLRLRR (i - 63)

def stree9LLRL (i : Nat) : State := if i < 126 then stree9LLRLL i else stree9LLRLR (i - 126)

def stree9LLRRLLLLL (i : Nat) : State := match i with | 0 => state9_756 | 1 => state9_757 | 2 => state9_758 | 3 => state9_759 | 4 => state9_760 | 5 => state9_761 | _ => state9_762

def stree9LLRRLLLLR (i : Nat) : State := match i with | 0 => state9_763 | 1 => state9_764 | 2 => state9_765 | 3 => state9_766 | 4 => state9_767 | 5 => state9_768 | 6 => state9_769 | _ => state9_770

def stree9LLRRLLLL (i : Nat) : State := if i < 7 then stree9LLRRLLLLL i else stree9LLRRLLLLR (i - 7)

def stree9LLRRLLLRL (i : Nat) : State := match i with | 0 => state9_771 | 1 => state9_772 | 2 => state9_773 | 3 => state9_774 | 4 => state9_775 | 5 => state9_776 | 6 => state9_777 | _ => state9_778

def stree9LLRRLLLRR (i : Nat) : State := match i with | 0 => state9_779 | 1 => state9_780 | 2 => state9_781 | 3 => state9_782 | 4 => state9_783 | 5 => state9_784 | 6 => state9_785 | _ => state9_786

def stree9LLRRLLLR (i : Nat) : State := if i < 8 then stree9LLRRLLLRL i else stree9LLRRLLLRR (i - 8)

def stree9LLRRLLL (i : Nat) : State := if i < 15 then stree9LLRRLLLL i else stree9LLRRLLLR (i - 15)

def stree9LLRRLLRLL (i : Nat) : State := match i with | 0 => state9_787 | 1 => state9_788 | 2 => state9_789 | 3 => state9_790 | 4 => state9_791 | 5 => state9_792 | 6 => state9_793 | _ => state9_794

def stree9LLRRLLRLR (i : Nat) : State := match i with | 0 => state9_795 | 1 => state9_796 | 2 => state9_797 | 3 => state9_798 | 4 => state9_799 | 5 => state9_800 | 6 => state9_801 | _ => state9_802

def stree9LLRRLLRL (i : Nat) : State := if i < 8 then stree9LLRRLLRLL i else stree9LLRRLLRLR (i - 8)

def stree9LLRRLLRRL (i : Nat) : State := match i with | 0 => state9_803 | 1 => state9_804 | 2 => state9_805 | 3 => state9_806 | 4 => state9_807 | 5 => state9_808 | 6 => state9_809 | _ => state9_810

def stree9LLRRLLRRR (i : Nat) : State := match i with | 0 => state9_811 | 1 => state9_812 | 2 => state9_813 | 3 => state9_814 | 4 => state9_815 | 5 => state9_816 | 6 => state9_817 | _ => state9_818

def stree9LLRRLLRR (i : Nat) : State := if i < 8 then stree9LLRRLLRRL i else stree9LLRRLLRRR (i - 8)

def stree9LLRRLLR (i : Nat) : State := if i < 16 then stree9LLRRLLRL i else stree9LLRRLLRR (i - 16)

def stree9LLRRLL (i : Nat) : State := if i < 31 then stree9LLRRLLL i else stree9LLRRLLR (i - 31)

def stree9LLRRLRLLL (i : Nat) : State := match i with | 0 => state9_819 | 1 => state9_820 | 2 => state9_821 | 3 => state9_822 | 4 => state9_823 | 5 => state9_824 | _ => state9_825

def stree9LLRRLRLLR (i : Nat) : State := match i with | 0 => state9_826 | 1 => state9_827 | 2 => state9_828 | 3 => state9_829 | 4 => state9_830 | 5 => state9_831 | 6 => state9_832 | _ => state9_833

def stree9LLRRLRLL (i : Nat) : State := if i < 7 then stree9LLRRLRLLL i else stree9LLRRLRLLR (i - 7)

def stree9LLRRLRLRL (i : Nat) : State := match i with | 0 => state9_834 | 1 => state9_835 | 2 => state9_836 | 3 => state9_837 | 4 => state9_838 | 5 => state9_839 | 6 => state9_840 | _ => state9_841

def stree9LLRRLRLRR (i : Nat) : State := match i with | 0 => state9_842 | 1 => state9_843 | 2 => state9_844 | 3 => state9_845 | 4 => state9_846 | 5 => state9_847 | 6 => state9_848 | _ => state9_849

def stree9LLRRLRLR (i : Nat) : State := if i < 8 then stree9LLRRLRLRL i else stree9LLRRLRLRR (i - 8)

def stree9LLRRLRL (i : Nat) : State := if i < 15 then stree9LLRRLRLL i else stree9LLRRLRLR (i - 15)

def stree9LLRRLRRLL (i : Nat) : State := match i with | 0 => state9_850 | 1 => state9_851 | 2 => state9_852 | 3 => state9_853 | 4 => state9_854 | 5 => state9_855 | 6 => state9_856 | _ => state9_857

def stree9LLRRLRRLR (i : Nat) : State := match i with | 0 => state9_858 | 1 => state9_859 | 2 => state9_860 | 3 => state9_861 | 4 => state9_862 | 5 => state9_863 | 6 => state9_864 | _ => state9_865

def stree9LLRRLRRL (i : Nat) : State := if i < 8 then stree9LLRRLRRLL i else stree9LLRRLRRLR (i - 8)

def stree9LLRRLRRRL (i : Nat) : State := match i with | 0 => state9_866 | 1 => state9_867 | 2 => state9_868 | 3 => state9_869 | 4 => state9_870 | 5 => state9_871 | 6 => state9_872 | _ => state9_873

def stree9LLRRLRRRR (i : Nat) : State := match i with | 0 => state9_874 | 1 => state9_875 | 2 => state9_876 | 3 => state9_877 | 4 => state9_878 | 5 => state9_879 | 6 => state9_880 | _ => state9_881

def stree9LLRRLRRR (i : Nat) : State := if i < 8 then stree9LLRRLRRRL i else stree9LLRRLRRRR (i - 8)

def stree9LLRRLRR (i : Nat) : State := if i < 16 then stree9LLRRLRRL i else stree9LLRRLRRR (i - 16)

def stree9LLRRLR (i : Nat) : State := if i < 31 then stree9LLRRLRL i else stree9LLRRLRR (i - 31)

def stree9LLRRL (i : Nat) : State := if i < 63 then stree9LLRRLL i else stree9LLRRLR (i - 63)

def stree9LLRRRLLLL (i : Nat) : State := match i with | 0 => state9_882 | 1 => state9_883 | 2 => state9_884 | 3 => state9_885 | 4 => state9_886 | 5 => state9_887 | _ => state9_888

def stree9LLRRRLLLR (i : Nat) : State := match i with | 0 => state9_889 | 1 => state9_890 | 2 => state9_891 | 3 => state9_892 | 4 => state9_893 | 5 => state9_894 | 6 => state9_895 | _ => state9_896

def stree9LLRRRLLL (i : Nat) : State := if i < 7 then stree9LLRRRLLLL i else stree9LLRRRLLLR (i - 7)

def stree9LLRRRLLRL (i : Nat) : State := match i with | 0 => state9_897 | 1 => state9_898 | 2 => state9_899 | 3 => state9_900 | 4 => state9_901 | 5 => state9_902 | 6 => state9_903 | _ => state9_904

def stree9LLRRRLLRR (i : Nat) : State := match i with | 0 => state9_905 | 1 => state9_906 | 2 => state9_907 | 3 => state9_908 | 4 => state9_909 | 5 => state9_910 | 6 => state9_911 | _ => state9_912

def stree9LLRRRLLR (i : Nat) : State := if i < 8 then stree9LLRRRLLRL i else stree9LLRRRLLRR (i - 8)

def stree9LLRRRLL (i : Nat) : State := if i < 15 then stree9LLRRRLLL i else stree9LLRRRLLR (i - 15)

def stree9LLRRRLRLL (i : Nat) : State := match i with | 0 => state9_913 | 1 => state9_914 | 2 => state9_915 | 3 => state9_916 | 4 => state9_917 | 5 => state9_918 | 6 => state9_919 | _ => state9_920

def stree9LLRRRLRLR (i : Nat) : State := match i with | 0 => state9_921 | 1 => state9_922 | 2 => state9_923 | 3 => state9_924 | 4 => state9_925 | 5 => state9_926 | 6 => state9_927 | _ => state9_928

def stree9LLRRRLRL (i : Nat) : State := if i < 8 then stree9LLRRRLRLL i else stree9LLRRRLRLR (i - 8)

def stree9LLRRRLRRL (i : Nat) : State := match i with | 0 => state9_929 | 1 => state9_930 | 2 => state9_931 | 3 => state9_932 | 4 => state9_933 | 5 => state9_934 | 6 => state9_935 | _ => state9_936

def stree9LLRRRLRRR (i : Nat) : State := match i with | 0 => state9_937 | 1 => state9_938 | 2 => state9_939 | 3 => state9_940 | 4 => state9_941 | 5 => state9_942 | 6 => state9_943 | _ => state9_944

def stree9LLRRRLRR (i : Nat) : State := if i < 8 then stree9LLRRRLRRL i else stree9LLRRRLRRR (i - 8)

def stree9LLRRRLR (i : Nat) : State := if i < 16 then stree9LLRRRLRL i else stree9LLRRRLRR (i - 16)

def stree9LLRRRL (i : Nat) : State := if i < 31 then stree9LLRRRLL i else stree9LLRRRLR (i - 31)

def stree9LLRRRRLLL (i : Nat) : State := match i with | 0 => state9_945 | 1 => state9_946 | 2 => state9_947 | 3 => state9_948 | 4 => state9_949 | 5 => state9_950 | _ => state9_951

def stree9LLRRRRLLR (i : Nat) : State := match i with | 0 => state9_952 | 1 => state9_953 | 2 => state9_954 | 3 => state9_955 | 4 => state9_956 | 5 => state9_957 | 6 => state9_958 | _ => state9_959

def stree9LLRRRRLL (i : Nat) : State := if i < 7 then stree9LLRRRRLLL i else stree9LLRRRRLLR (i - 7)

def stree9LLRRRRLRL (i : Nat) : State := match i with | 0 => state9_960 | 1 => state9_961 | 2 => state9_962 | 3 => state9_963 | 4 => state9_964 | 5 => state9_965 | 6 => state9_966 | _ => state9_967

def stree9LLRRRRLRR (i : Nat) : State := match i with | 0 => state9_968 | 1 => state9_969 | 2 => state9_970 | 3 => state9_971 | 4 => state9_972 | 5 => state9_973 | 6 => state9_974 | _ => state9_975

def stree9LLRRRRLR (i : Nat) : State := if i < 8 then stree9LLRRRRLRL i else stree9LLRRRRLRR (i - 8)

def stree9LLRRRRL (i : Nat) : State := if i < 15 then stree9LLRRRRLL i else stree9LLRRRRLR (i - 15)

def stree9LLRRRRRLL (i : Nat) : State := match i with | 0 => state9_976 | 1 => state9_977 | 2 => state9_978 | 3 => state9_979 | 4 => state9_980 | 5 => state9_981 | 6 => state9_982 | _ => state9_983

def stree9LLRRRRRLR (i : Nat) : State := match i with | 0 => state9_984 | 1 => state9_985 | 2 => state9_986 | 3 => state9_987 | 4 => state9_988 | 5 => state9_989 | 6 => state9_990 | _ => state9_991

def stree9LLRRRRRL (i : Nat) : State := if i < 8 then stree9LLRRRRRLL i else stree9LLRRRRRLR (i - 8)

def stree9LLRRRRRRL (i : Nat) : State := match i with | 0 => state9_992 | 1 => state9_993 | 2 => state9_994 | 3 => state9_995 | 4 => state9_996 | 5 => state9_997 | 6 => state9_998 | _ => state9_999

def stree9LLRRRRRRR (i : Nat) : State := match i with | 0 => state9_1000 | 1 => state9_1001 | 2 => state9_1002 | 3 => state9_1003 | 4 => state9_1004 | 5 => state9_1005 | 6 => state9_1006 | _ => state9_1007

def stree9LLRRRRRR (i : Nat) : State := if i < 8 then stree9LLRRRRRRL i else stree9LLRRRRRRR (i - 8)

def stree9LLRRRRR (i : Nat) : State := if i < 16 then stree9LLRRRRRL i else stree9LLRRRRRR (i - 16)

def stree9LLRRRR (i : Nat) : State := if i < 31 then stree9LLRRRRL i else stree9LLRRRRR (i - 31)

def stree9LLRRR (i : Nat) : State := if i < 63 then stree9LLRRRL i else stree9LLRRRR (i - 63)

def stree9LLRR (i : Nat) : State := if i < 126 then stree9LLRRL i else stree9LLRRR (i - 126)

def stree9LLR (i : Nat) : State := if i < 252 then stree9LLRL i else stree9LLRR (i - 252)

def stree9LL (i : Nat) : State := if i < 504 then stree9LLL i else stree9LLR (i - 504)

def stree9LRLLLLLLL (i : Nat) : State := match i with | 0 => state9_1008 | 1 => state9_1009 | 2 => state9_1010 | 3 => state9_1011 | 4 => state9_1012 | 5 => state9_1013 | _ => state9_1014

def stree9LRLLLLLLR (i : Nat) : State := match i with | 0 => state9_1015 | 1 => state9_1016 | 2 => state9_1017 | 3 => state9_1018 | 4 => state9_1019 | 5 => state9_1020 | 6 => state9_1021 | _ => state9_1022

def stree9LRLLLLLL (i : Nat) : State := if i < 7 then stree9LRLLLLLLL i else stree9LRLLLLLLR (i - 7)

def stree9LRLLLLLRL (i : Nat) : State := match i with | 0 => state9_1023 | 1 => state9_1024 | 2 => state9_1025 | 3 => state9_1026 | 4 => state9_1027 | 5 => state9_1028 | 6 => state9_1029 | _ => state9_1030

def stree9LRLLLLLRR (i : Nat) : State := match i with | 0 => state9_1031 | 1 => state9_1032 | 2 => state9_1033 | 3 => state9_1034 | 4 => state9_1035 | 5 => state9_1036 | 6 => state9_1037 | _ => state9_1038

def stree9LRLLLLLR (i : Nat) : State := if i < 8 then stree9LRLLLLLRL i else stree9LRLLLLLRR (i - 8)

def stree9LRLLLLL (i : Nat) : State := if i < 15 then stree9LRLLLLLL i else stree9LRLLLLLR (i - 15)

def stree9LRLLLLRLL (i : Nat) : State := match i with | 0 => state9_1039 | 1 => state9_1040 | 2 => state9_1041 | 3 => state9_1042 | 4 => state9_1043 | 5 => state9_1044 | 6 => state9_1045 | _ => state9_1046

def stree9LRLLLLRLR (i : Nat) : State := match i with | 0 => state9_1047 | 1 => state9_1048 | 2 => state9_1049 | 3 => state9_1050 | 4 => state9_1051 | 5 => state9_1052 | 6 => state9_1053 | _ => state9_1054

def stree9LRLLLLRL (i : Nat) : State := if i < 8 then stree9LRLLLLRLL i else stree9LRLLLLRLR (i - 8)

def stree9LRLLLLRRL (i : Nat) : State := match i with | 0 => state9_1055 | 1 => state9_1056 | 2 => state9_1057 | 3 => state9_1058 | 4 => state9_1059 | 5 => state9_1060 | 6 => state9_1061 | _ => state9_1062

def stree9LRLLLLRRR (i : Nat) : State := match i with | 0 => state9_1063 | 1 => state9_1064 | 2 => state9_1065 | 3 => state9_1066 | 4 => state9_1067 | 5 => state9_1068 | 6 => state9_1069 | _ => state9_1070

def stree9LRLLLLRR (i : Nat) : State := if i < 8 then stree9LRLLLLRRL i else stree9LRLLLLRRR (i - 8)

def stree9LRLLLLR (i : Nat) : State := if i < 16 then stree9LRLLLLRL i else stree9LRLLLLRR (i - 16)

def stree9LRLLLL (i : Nat) : State := if i < 31 then stree9LRLLLLL i else stree9LRLLLLR (i - 31)

def stree9LRLLLRLLL (i : Nat) : State := match i with | 0 => state9_1071 | 1 => state9_1072 | 2 => state9_1073 | 3 => state9_1074 | 4 => state9_1075 | 5 => state9_1076 | _ => state9_1077

def stree9LRLLLRLLR (i : Nat) : State := match i with | 0 => state9_1078 | 1 => state9_1079 | 2 => state9_1080 | 3 => state9_1081 | 4 => state9_1082 | 5 => state9_1083 | 6 => state9_1084 | _ => state9_1085

def stree9LRLLLRLL (i : Nat) : State := if i < 7 then stree9LRLLLRLLL i else stree9LRLLLRLLR (i - 7)

def stree9LRLLLRLRL (i : Nat) : State := match i with | 0 => state9_1086 | 1 => state9_1087 | 2 => state9_1088 | 3 => state9_1089 | 4 => state9_1090 | 5 => state9_1091 | 6 => state9_1092 | _ => state9_1093

def stree9LRLLLRLRR (i : Nat) : State := match i with | 0 => state9_1094 | 1 => state9_1095 | 2 => state9_1096 | 3 => state9_1097 | 4 => state9_1098 | 5 => state9_1099 | 6 => state9_1100 | _ => state9_1101

def stree9LRLLLRLR (i : Nat) : State := if i < 8 then stree9LRLLLRLRL i else stree9LRLLLRLRR (i - 8)

def stree9LRLLLRL (i : Nat) : State := if i < 15 then stree9LRLLLRLL i else stree9LRLLLRLR (i - 15)

def stree9LRLLLRRLL (i : Nat) : State := match i with | 0 => state9_1102 | 1 => state9_1103 | 2 => state9_1104 | 3 => state9_1105 | 4 => state9_1106 | 5 => state9_1107 | 6 => state9_1108 | _ => state9_1109

def stree9LRLLLRRLR (i : Nat) : State := match i with | 0 => state9_1110 | 1 => state9_1111 | 2 => state9_1112 | 3 => state9_1113 | 4 => state9_1114 | 5 => state9_1115 | 6 => state9_1116 | _ => state9_1117

def stree9LRLLLRRL (i : Nat) : State := if i < 8 then stree9LRLLLRRLL i else stree9LRLLLRRLR (i - 8)

def stree9LRLLLRRRL (i : Nat) : State := match i with | 0 => state9_1118 | 1 => state9_1119 | 2 => state9_1120 | 3 => state9_1121 | 4 => state9_1122 | 5 => state9_1123 | 6 => state9_1124 | _ => state9_1125

def stree9LRLLLRRRR (i : Nat) : State := match i with | 0 => state9_1126 | 1 => state9_1127 | 2 => state9_1128 | 3 => state9_1129 | 4 => state9_1130 | 5 => state9_1131 | 6 => state9_1132 | _ => state9_1133

def stree9LRLLLRRR (i : Nat) : State := if i < 8 then stree9LRLLLRRRL i else stree9LRLLLRRRR (i - 8)

def stree9LRLLLRR (i : Nat) : State := if i < 16 then stree9LRLLLRRL i else stree9LRLLLRRR (i - 16)

def stree9LRLLLR (i : Nat) : State := if i < 31 then stree9LRLLLRL i else stree9LRLLLRR (i - 31)

def stree9LRLLL (i : Nat) : State := if i < 63 then stree9LRLLLL i else stree9LRLLLR (i - 63)

def stree9LRLLRLLLL (i : Nat) : State := match i with | 0 => state9_1134 | 1 => state9_1135 | 2 => state9_1136 | 3 => state9_1137 | 4 => state9_1138 | 5 => state9_1139 | _ => state9_1140

def stree9LRLLRLLLR (i : Nat) : State := match i with | 0 => state9_1141 | 1 => state9_1142 | 2 => state9_1143 | 3 => state9_1144 | 4 => state9_1145 | 5 => state9_1146 | 6 => state9_1147 | _ => state9_1148

def stree9LRLLRLLL (i : Nat) : State := if i < 7 then stree9LRLLRLLLL i else stree9LRLLRLLLR (i - 7)

def stree9LRLLRLLRL (i : Nat) : State := match i with | 0 => state9_1149 | 1 => state9_1150 | 2 => state9_1151 | 3 => state9_1152 | 4 => state9_1153 | 5 => state9_1154 | 6 => state9_1155 | _ => state9_1156

def stree9LRLLRLLRR (i : Nat) : State := match i with | 0 => state9_1157 | 1 => state9_1158 | 2 => state9_1159 | 3 => state9_1160 | 4 => state9_1161 | 5 => state9_1162 | 6 => state9_1163 | _ => state9_1164

def stree9LRLLRLLR (i : Nat) : State := if i < 8 then stree9LRLLRLLRL i else stree9LRLLRLLRR (i - 8)

def stree9LRLLRLL (i : Nat) : State := if i < 15 then stree9LRLLRLLL i else stree9LRLLRLLR (i - 15)

def stree9LRLLRLRLL (i : Nat) : State := match i with | 0 => state9_1165 | 1 => state9_1166 | 2 => state9_1167 | 3 => state9_1168 | 4 => state9_1169 | 5 => state9_1170 | 6 => state9_1171 | _ => state9_1172

def stree9LRLLRLRLR (i : Nat) : State := match i with | 0 => state9_1173 | 1 => state9_1174 | 2 => state9_1175 | 3 => state9_1176 | 4 => state9_1177 | 5 => state9_1178 | 6 => state9_1179 | _ => state9_1180

def stree9LRLLRLRL (i : Nat) : State := if i < 8 then stree9LRLLRLRLL i else stree9LRLLRLRLR (i - 8)

def stree9LRLLRLRRL (i : Nat) : State := match i with | 0 => state9_1181 | 1 => state9_1182 | 2 => state9_1183 | 3 => state9_1184 | 4 => state9_1185 | 5 => state9_1186 | 6 => state9_1187 | _ => state9_1188

def stree9LRLLRLRRR (i : Nat) : State := match i with | 0 => state9_1189 | 1 => state9_1190 | 2 => state9_1191 | 3 => state9_1192 | 4 => state9_1193 | 5 => state9_1194 | 6 => state9_1195 | _ => state9_1196

def stree9LRLLRLRR (i : Nat) : State := if i < 8 then stree9LRLLRLRRL i else stree9LRLLRLRRR (i - 8)

def stree9LRLLRLR (i : Nat) : State := if i < 16 then stree9LRLLRLRL i else stree9LRLLRLRR (i - 16)

def stree9LRLLRL (i : Nat) : State := if i < 31 then stree9LRLLRLL i else stree9LRLLRLR (i - 31)

def stree9LRLLRRLLL (i : Nat) : State := match i with | 0 => state9_1197 | 1 => state9_1198 | 2 => state9_1199 | 3 => state9_1200 | 4 => state9_1201 | 5 => state9_1202 | _ => state9_1203

def stree9LRLLRRLLR (i : Nat) : State := match i with | 0 => state9_1204 | 1 => state9_1205 | 2 => state9_1206 | 3 => state9_1207 | 4 => state9_1208 | 5 => state9_1209 | 6 => state9_1210 | _ => state9_1211

def stree9LRLLRRLL (i : Nat) : State := if i < 7 then stree9LRLLRRLLL i else stree9LRLLRRLLR (i - 7)

def stree9LRLLRRLRL (i : Nat) : State := match i with | 0 => state9_1212 | 1 => state9_1213 | 2 => state9_1214 | 3 => state9_1215 | 4 => state9_1216 | 5 => state9_1217 | 6 => state9_1218 | _ => state9_1219

def stree9LRLLRRLRR (i : Nat) : State := match i with | 0 => state9_1220 | 1 => state9_1221 | 2 => state9_1222 | 3 => state9_1223 | 4 => state9_1224 | 5 => state9_1225 | 6 => state9_1226 | _ => state9_1227

def stree9LRLLRRLR (i : Nat) : State := if i < 8 then stree9LRLLRRLRL i else stree9LRLLRRLRR (i - 8)

def stree9LRLLRRL (i : Nat) : State := if i < 15 then stree9LRLLRRLL i else stree9LRLLRRLR (i - 15)

def stree9LRLLRRRLL (i : Nat) : State := match i with | 0 => state9_1228 | 1 => state9_1229 | 2 => state9_1230 | 3 => state9_1231 | 4 => state9_1232 | 5 => state9_1233 | 6 => state9_1234 | _ => state9_1235

def stree9LRLLRRRLR (i : Nat) : State := match i with | 0 => state9_1236 | 1 => state9_1237 | 2 => state9_1238 | 3 => state9_1239 | 4 => state9_1240 | 5 => state9_1241 | 6 => state9_1242 | _ => state9_1243

def stree9LRLLRRRL (i : Nat) : State := if i < 8 then stree9LRLLRRRLL i else stree9LRLLRRRLR (i - 8)

def stree9LRLLRRRRL (i : Nat) : State := match i with | 0 => state9_1244 | 1 => state9_1245 | 2 => state9_1246 | 3 => state9_1247 | 4 => state9_1248 | 5 => state9_1249 | 6 => state9_1250 | _ => state9_1251

def stree9LRLLRRRRR (i : Nat) : State := match i with | 0 => state9_1252 | 1 => state9_1253 | 2 => state9_1254 | 3 => state9_1255 | 4 => state9_1256 | 5 => state9_1257 | 6 => state9_1258 | _ => state9_1259

def stree9LRLLRRRR (i : Nat) : State := if i < 8 then stree9LRLLRRRRL i else stree9LRLLRRRRR (i - 8)

def stree9LRLLRRR (i : Nat) : State := if i < 16 then stree9LRLLRRRL i else stree9LRLLRRRR (i - 16)

def stree9LRLLRR (i : Nat) : State := if i < 31 then stree9LRLLRRL i else stree9LRLLRRR (i - 31)

def stree9LRLLR (i : Nat) : State := if i < 63 then stree9LRLLRL i else stree9LRLLRR (i - 63)

def stree9LRLL (i : Nat) : State := if i < 126 then stree9LRLLL i else stree9LRLLR (i - 126)

def stree9LRLRLLLLL (i : Nat) : State := match i with | 0 => state9_1260 | 1 => state9_1261 | 2 => state9_1262 | 3 => state9_1263 | 4 => state9_1264 | 5 => state9_1265 | _ => state9_1266

def stree9LRLRLLLLR (i : Nat) : State := match i with | 0 => state9_1267 | 1 => state9_1268 | 2 => state9_1269 | 3 => state9_1270 | 4 => state9_1271 | 5 => state9_1272 | 6 => state9_1273 | _ => state9_1274

def stree9LRLRLLLL (i : Nat) : State := if i < 7 then stree9LRLRLLLLL i else stree9LRLRLLLLR (i - 7)

def stree9LRLRLLLRL (i : Nat) : State := match i with | 0 => state9_1275 | 1 => state9_1276 | 2 => state9_1277 | 3 => state9_1278 | 4 => state9_1279 | 5 => state9_1280 | 6 => state9_1281 | _ => state9_1282

def stree9LRLRLLLRR (i : Nat) : State := match i with | 0 => state9_1283 | 1 => state9_1284 | 2 => state9_1285 | 3 => state9_1286 | 4 => state9_1287 | 5 => state9_1288 | 6 => state9_1289 | _ => state9_1290

def stree9LRLRLLLR (i : Nat) : State := if i < 8 then stree9LRLRLLLRL i else stree9LRLRLLLRR (i - 8)

def stree9LRLRLLL (i : Nat) : State := if i < 15 then stree9LRLRLLLL i else stree9LRLRLLLR (i - 15)

def stree9LRLRLLRLL (i : Nat) : State := match i with | 0 => state9_1291 | 1 => state9_1292 | 2 => state9_1293 | 3 => state9_1294 | 4 => state9_1295 | 5 => state9_1296 | 6 => state9_1297 | _ => state9_1298

def stree9LRLRLLRLR (i : Nat) : State := match i with | 0 => state9_1299 | 1 => state9_1300 | 2 => state9_1301 | 3 => state9_1302 | 4 => state9_1303 | 5 => state9_1304 | 6 => state9_1305 | _ => state9_1306

def stree9LRLRLLRL (i : Nat) : State := if i < 8 then stree9LRLRLLRLL i else stree9LRLRLLRLR (i - 8)

def stree9LRLRLLRRL (i : Nat) : State := match i with | 0 => state9_1307 | 1 => state9_1308 | 2 => state9_1309 | 3 => state9_1310 | 4 => state9_1311 | 5 => state9_1312 | 6 => state9_1313 | _ => state9_1314

def stree9LRLRLLRRR (i : Nat) : State := match i with | 0 => state9_1315 | 1 => state9_1316 | 2 => state9_1317 | 3 => state9_1318 | 4 => state9_1319 | 5 => state9_1320 | 6 => state9_1321 | _ => state9_1322

def stree9LRLRLLRR (i : Nat) : State := if i < 8 then stree9LRLRLLRRL i else stree9LRLRLLRRR (i - 8)

def stree9LRLRLLR (i : Nat) : State := if i < 16 then stree9LRLRLLRL i else stree9LRLRLLRR (i - 16)

def stree9LRLRLL (i : Nat) : State := if i < 31 then stree9LRLRLLL i else stree9LRLRLLR (i - 31)

def stree9LRLRLRLLL (i : Nat) : State := match i with | 0 => state9_1323 | 1 => state9_1324 | 2 => state9_1325 | 3 => state9_1326 | 4 => state9_1327 | 5 => state9_1328 | _ => state9_1329

def stree9LRLRLRLLR (i : Nat) : State := match i with | 0 => state9_1330 | 1 => state9_1331 | 2 => state9_1332 | 3 => state9_1333 | 4 => state9_1334 | 5 => state9_1335 | 6 => state9_1336 | _ => state9_1337

def stree9LRLRLRLL (i : Nat) : State := if i < 7 then stree9LRLRLRLLL i else stree9LRLRLRLLR (i - 7)

def stree9LRLRLRLRL (i : Nat) : State := match i with | 0 => state9_1338 | 1 => state9_1339 | 2 => state9_1340 | 3 => state9_1341 | 4 => state9_1342 | 5 => state9_1343 | 6 => state9_1344 | _ => state9_1345

def stree9LRLRLRLRR (i : Nat) : State := match i with | 0 => state9_1346 | 1 => state9_1347 | 2 => state9_1348 | 3 => state9_1349 | 4 => state9_1350 | 5 => state9_1351 | 6 => state9_1352 | _ => state9_1353

def stree9LRLRLRLR (i : Nat) : State := if i < 8 then stree9LRLRLRLRL i else stree9LRLRLRLRR (i - 8)

def stree9LRLRLRL (i : Nat) : State := if i < 15 then stree9LRLRLRLL i else stree9LRLRLRLR (i - 15)

def stree9LRLRLRRLL (i : Nat) : State := match i with | 0 => state9_1354 | 1 => state9_1355 | 2 => state9_1356 | 3 => state9_1357 | 4 => state9_1358 | 5 => state9_1359 | 6 => state9_1360 | _ => state9_1361

def stree9LRLRLRRLR (i : Nat) : State := match i with | 0 => state9_1362 | 1 => state9_1363 | 2 => state9_1364 | 3 => state9_1365 | 4 => state9_1366 | 5 => state9_1367 | 6 => state9_1368 | _ => state9_1369

def stree9LRLRLRRL (i : Nat) : State := if i < 8 then stree9LRLRLRRLL i else stree9LRLRLRRLR (i - 8)

def stree9LRLRLRRRL (i : Nat) : State := match i with | 0 => state9_1370 | 1 => state9_1371 | 2 => state9_1372 | 3 => state9_1373 | 4 => state9_1374 | 5 => state9_1375 | 6 => state9_1376 | _ => state9_1377

def stree9LRLRLRRRR (i : Nat) : State := match i with | 0 => state9_1378 | 1 => state9_1379 | 2 => state9_1380 | 3 => state9_1381 | 4 => state9_1382 | 5 => state9_1383 | 6 => state9_1384 | _ => state9_1385

def stree9LRLRLRRR (i : Nat) : State := if i < 8 then stree9LRLRLRRRL i else stree9LRLRLRRRR (i - 8)

def stree9LRLRLRR (i : Nat) : State := if i < 16 then stree9LRLRLRRL i else stree9LRLRLRRR (i - 16)

def stree9LRLRLR (i : Nat) : State := if i < 31 then stree9LRLRLRL i else stree9LRLRLRR (i - 31)

def stree9LRLRL (i : Nat) : State := if i < 63 then stree9LRLRLL i else stree9LRLRLR (i - 63)

def stree9LRLRRLLLL (i : Nat) : State := match i with | 0 => state9_1386 | 1 => state9_1387 | 2 => state9_1388 | 3 => state9_1389 | 4 => state9_1390 | 5 => state9_1391 | _ => state9_1392

def stree9LRLRRLLLR (i : Nat) : State := match i with | 0 => state9_1393 | 1 => state9_1394 | 2 => state9_1395 | 3 => state9_1396 | 4 => state9_1397 | 5 => state9_1398 | 6 => state9_1399 | _ => state9_1400

def stree9LRLRRLLL (i : Nat) : State := if i < 7 then stree9LRLRRLLLL i else stree9LRLRRLLLR (i - 7)

def stree9LRLRRLLRL (i : Nat) : State := match i with | 0 => state9_1401 | 1 => state9_1402 | 2 => state9_1403 | 3 => state9_1404 | 4 => state9_1405 | 5 => state9_1406 | 6 => state9_1407 | _ => state9_1408

def stree9LRLRRLLRR (i : Nat) : State := match i with | 0 => state9_1409 | 1 => state9_1410 | 2 => state9_1411 | 3 => state9_1412 | 4 => state9_1413 | 5 => state9_1414 | 6 => state9_1415 | _ => state9_1416

def stree9LRLRRLLR (i : Nat) : State := if i < 8 then stree9LRLRRLLRL i else stree9LRLRRLLRR (i - 8)

def stree9LRLRRLL (i : Nat) : State := if i < 15 then stree9LRLRRLLL i else stree9LRLRRLLR (i - 15)

def stree9LRLRRLRLL (i : Nat) : State := match i with | 0 => state9_1417 | 1 => state9_1418 | 2 => state9_1419 | 3 => state9_1420 | 4 => state9_1421 | 5 => state9_1422 | 6 => state9_1423 | _ => state9_1424

def stree9LRLRRLRLR (i : Nat) : State := match i with | 0 => state9_1425 | 1 => state9_1426 | 2 => state9_1427 | 3 => state9_1428 | 4 => state9_1429 | 5 => state9_1430 | 6 => state9_1431 | _ => state9_1432

def stree9LRLRRLRL (i : Nat) : State := if i < 8 then stree9LRLRRLRLL i else stree9LRLRRLRLR (i - 8)

def stree9LRLRRLRRL (i : Nat) : State := match i with | 0 => state9_1433 | 1 => state9_1434 | 2 => state9_1435 | 3 => state9_1436 | 4 => state9_1437 | 5 => state9_1438 | 6 => state9_1439 | _ => state9_1440

def stree9LRLRRLRRR (i : Nat) : State := match i with | 0 => state9_1441 | 1 => state9_1442 | 2 => state9_1443 | 3 => state9_1444 | 4 => state9_1445 | 5 => state9_1446 | 6 => state9_1447 | _ => state9_1448

def stree9LRLRRLRR (i : Nat) : State := if i < 8 then stree9LRLRRLRRL i else stree9LRLRRLRRR (i - 8)

def stree9LRLRRLR (i : Nat) : State := if i < 16 then stree9LRLRRLRL i else stree9LRLRRLRR (i - 16)

def stree9LRLRRL (i : Nat) : State := if i < 31 then stree9LRLRRLL i else stree9LRLRRLR (i - 31)

def stree9LRLRRRLLL (i : Nat) : State := match i with | 0 => state9_1449 | 1 => state9_1450 | 2 => state9_1451 | 3 => state9_1452 | 4 => state9_1453 | 5 => state9_1454 | _ => state9_1455

def stree9LRLRRRLLR (i : Nat) : State := match i with | 0 => state9_1456 | 1 => state9_1457 | 2 => state9_1458 | 3 => state9_1459 | 4 => state9_1460 | 5 => state9_1461 | 6 => state9_1462 | _ => state9_1463

def stree9LRLRRRLL (i : Nat) : State := if i < 7 then stree9LRLRRRLLL i else stree9LRLRRRLLR (i - 7)

def stree9LRLRRRLRL (i : Nat) : State := match i with | 0 => state9_1464 | 1 => state9_1465 | 2 => state9_1466 | 3 => state9_1467 | 4 => state9_1468 | 5 => state9_1469 | 6 => state9_1470 | _ => state9_1471

def stree9LRLRRRLRR (i : Nat) : State := match i with | 0 => state9_1472 | 1 => state9_1473 | 2 => state9_1474 | 3 => state9_1475 | 4 => state9_1476 | 5 => state9_1477 | 6 => state9_1478 | _ => state9_1479

def stree9LRLRRRLR (i : Nat) : State := if i < 8 then stree9LRLRRRLRL i else stree9LRLRRRLRR (i - 8)

def stree9LRLRRRL (i : Nat) : State := if i < 15 then stree9LRLRRRLL i else stree9LRLRRRLR (i - 15)

def stree9LRLRRRRLL (i : Nat) : State := match i with | 0 => state9_1480 | 1 => state9_1481 | 2 => state9_1482 | 3 => state9_1483 | 4 => state9_1484 | 5 => state9_1485 | 6 => state9_1486 | _ => state9_1487

def stree9LRLRRRRLR (i : Nat) : State := match i with | 0 => state9_1488 | 1 => state9_1489 | 2 => state9_1490 | 3 => state9_1491 | 4 => state9_1492 | 5 => state9_1493 | 6 => state9_1494 | _ => state9_1495

def stree9LRLRRRRL (i : Nat) : State := if i < 8 then stree9LRLRRRRLL i else stree9LRLRRRRLR (i - 8)

def stree9LRLRRRRRL (i : Nat) : State := match i with | 0 => state9_1496 | 1 => state9_1497 | 2 => state9_1498 | 3 => state9_1499 | 4 => state9_1500 | 5 => state9_1501 | 6 => state9_1502 | _ => state9_1503

def stree9LRLRRRRRR (i : Nat) : State := match i with | 0 => state9_1504 | 1 => state9_1505 | 2 => state9_1506 | 3 => state9_1507 | 4 => state9_1508 | 5 => state9_1509 | 6 => state9_1510 | _ => state9_1511

def stree9LRLRRRRR (i : Nat) : State := if i < 8 then stree9LRLRRRRRL i else stree9LRLRRRRRR (i - 8)

def stree9LRLRRRR (i : Nat) : State := if i < 16 then stree9LRLRRRRL i else stree9LRLRRRRR (i - 16)

def stree9LRLRRR (i : Nat) : State := if i < 31 then stree9LRLRRRL i else stree9LRLRRRR (i - 31)

def stree9LRLRR (i : Nat) : State := if i < 63 then stree9LRLRRL i else stree9LRLRRR (i - 63)

def stree9LRLR (i : Nat) : State := if i < 126 then stree9LRLRL i else stree9LRLRR (i - 126)

def stree9LRL (i : Nat) : State := if i < 252 then stree9LRLL i else stree9LRLR (i - 252)

def stree9LRRLLLLLL (i : Nat) : State := match i with | 0 => state9_1512 | 1 => state9_1513 | 2 => state9_1514 | 3 => state9_1515 | 4 => state9_1516 | 5 => state9_1517 | _ => state9_1518

def stree9LRRLLLLLR (i : Nat) : State := match i with | 0 => state9_1519 | 1 => state9_1520 | 2 => state9_1521 | 3 => state9_1522 | 4 => state9_1523 | 5 => state9_1524 | 6 => state9_1525 | _ => state9_1526

def stree9LRRLLLLL (i : Nat) : State := if i < 7 then stree9LRRLLLLLL i else stree9LRRLLLLLR (i - 7)

def stree9LRRLLLLRL (i : Nat) : State := match i with | 0 => state9_1527 | 1 => state9_1528 | 2 => state9_1529 | 3 => state9_1530 | 4 => state9_1531 | 5 => state9_1532 | 6 => state9_1533 | _ => state9_1534

def stree9LRRLLLLRR (i : Nat) : State := match i with | 0 => state9_1535 | 1 => state9_1536 | 2 => state9_1537 | 3 => state9_1538 | 4 => state9_1539 | 5 => state9_1540 | 6 => state9_1541 | _ => state9_1542

def stree9LRRLLLLR (i : Nat) : State := if i < 8 then stree9LRRLLLLRL i else stree9LRRLLLLRR (i - 8)

def stree9LRRLLLL (i : Nat) : State := if i < 15 then stree9LRRLLLLL i else stree9LRRLLLLR (i - 15)

def stree9LRRLLLRLL (i : Nat) : State := match i with | 0 => state9_1543 | 1 => state9_1544 | 2 => state9_1545 | 3 => state9_1546 | 4 => state9_1547 | 5 => state9_1548 | 6 => state9_1549 | _ => state9_1550

def stree9LRRLLLRLR (i : Nat) : State := match i with | 0 => state9_1551 | 1 => state9_1552 | 2 => state9_1553 | 3 => state9_1554 | 4 => state9_1555 | 5 => state9_1556 | 6 => state9_1557 | _ => state9_1558

def stree9LRRLLLRL (i : Nat) : State := if i < 8 then stree9LRRLLLRLL i else stree9LRRLLLRLR (i - 8)

def stree9LRRLLLRRL (i : Nat) : State := match i with | 0 => state9_1559 | 1 => state9_1560 | 2 => state9_1561 | 3 => state9_1562 | 4 => state9_1563 | 5 => state9_1564 | 6 => state9_1565 | _ => state9_1566

def stree9LRRLLLRRR (i : Nat) : State := match i with | 0 => state9_1567 | 1 => state9_1568 | 2 => state9_1569 | 3 => state9_1570 | 4 => state9_1571 | 5 => state9_1572 | 6 => state9_1573 | _ => state9_1574

def stree9LRRLLLRR (i : Nat) : State := if i < 8 then stree9LRRLLLRRL i else stree9LRRLLLRRR (i - 8)

def stree9LRRLLLR (i : Nat) : State := if i < 16 then stree9LRRLLLRL i else stree9LRRLLLRR (i - 16)

def stree9LRRLLL (i : Nat) : State := if i < 31 then stree9LRRLLLL i else stree9LRRLLLR (i - 31)

def stree9LRRLLRLLL (i : Nat) : State := match i with | 0 => state9_1575 | 1 => state9_1576 | 2 => state9_1577 | 3 => state9_1578 | 4 => state9_1579 | 5 => state9_1580 | _ => state9_1581

def stree9LRRLLRLLR (i : Nat) : State := match i with | 0 => state9_1582 | 1 => state9_1583 | 2 => state9_1584 | 3 => state9_1585 | 4 => state9_1586 | 5 => state9_1587 | 6 => state9_1588 | _ => state9_1589

def stree9LRRLLRLL (i : Nat) : State := if i < 7 then stree9LRRLLRLLL i else stree9LRRLLRLLR (i - 7)

def stree9LRRLLRLRL (i : Nat) : State := match i with | 0 => state9_1590 | 1 => state9_1591 | 2 => state9_1592 | 3 => state9_1593 | 4 => state9_1594 | 5 => state9_1595 | 6 => state9_1596 | _ => state9_1597

def stree9LRRLLRLRR (i : Nat) : State := match i with | 0 => state9_1598 | 1 => state9_1599 | 2 => state9_1600 | 3 => state9_1601 | 4 => state9_1602 | 5 => state9_1603 | 6 => state9_1604 | _ => state9_1605

def stree9LRRLLRLR (i : Nat) : State := if i < 8 then stree9LRRLLRLRL i else stree9LRRLLRLRR (i - 8)

def stree9LRRLLRL (i : Nat) : State := if i < 15 then stree9LRRLLRLL i else stree9LRRLLRLR (i - 15)

def stree9LRRLLRRLL (i : Nat) : State := match i with | 0 => state9_1606 | 1 => state9_1607 | 2 => state9_1608 | 3 => state9_1609 | 4 => state9_1610 | 5 => state9_1611 | 6 => state9_1612 | _ => state9_1613

def stree9LRRLLRRLR (i : Nat) : State := match i with | 0 => state9_1614 | 1 => state9_1615 | 2 => state9_1616 | 3 => state9_1617 | 4 => state9_1618 | 5 => state9_1619 | 6 => state9_1620 | _ => state9_1621

def stree9LRRLLRRL (i : Nat) : State := if i < 8 then stree9LRRLLRRLL i else stree9LRRLLRRLR (i - 8)

def stree9LRRLLRRRL (i : Nat) : State := match i with | 0 => state9_1622 | 1 => state9_1623 | 2 => state9_1624 | 3 => state9_1625 | 4 => state9_1626 | 5 => state9_1627 | 6 => state9_1628 | _ => state9_1629

def stree9LRRLLRRRR (i : Nat) : State := match i with | 0 => state9_1630 | 1 => state9_1631 | 2 => state9_1632 | 3 => state9_1633 | 4 => state9_1634 | 5 => state9_1635 | 6 => state9_1636 | _ => state9_1637

def stree9LRRLLRRR (i : Nat) : State := if i < 8 then stree9LRRLLRRRL i else stree9LRRLLRRRR (i - 8)

def stree9LRRLLRR (i : Nat) : State := if i < 16 then stree9LRRLLRRL i else stree9LRRLLRRR (i - 16)

def stree9LRRLLR (i : Nat) : State := if i < 31 then stree9LRRLLRL i else stree9LRRLLRR (i - 31)

def stree9LRRLL (i : Nat) : State := if i < 63 then stree9LRRLLL i else stree9LRRLLR (i - 63)

def stree9LRRLRLLLL (i : Nat) : State := match i with | 0 => state9_1638 | 1 => state9_1639 | 2 => state9_1640 | 3 => state9_1641 | 4 => state9_1642 | 5 => state9_1643 | _ => state9_1644

def stree9LRRLRLLLR (i : Nat) : State := match i with | 0 => state9_1645 | 1 => state9_1646 | 2 => state9_1647 | 3 => state9_1648 | 4 => state9_1649 | 5 => state9_1650 | 6 => state9_1651 | _ => state9_1652

def stree9LRRLRLLL (i : Nat) : State := if i < 7 then stree9LRRLRLLLL i else stree9LRRLRLLLR (i - 7)

def stree9LRRLRLLRL (i : Nat) : State := match i with | 0 => state9_1653 | 1 => state9_1654 | 2 => state9_1655 | 3 => state9_1656 | 4 => state9_1657 | 5 => state9_1658 | 6 => state9_1659 | _ => state9_1660

def stree9LRRLRLLRR (i : Nat) : State := match i with | 0 => state9_1661 | 1 => state9_1662 | 2 => state9_1663 | 3 => state9_1664 | 4 => state9_1665 | 5 => state9_1666 | 6 => state9_1667 | _ => state9_1668

def stree9LRRLRLLR (i : Nat) : State := if i < 8 then stree9LRRLRLLRL i else stree9LRRLRLLRR (i - 8)

def stree9LRRLRLL (i : Nat) : State := if i < 15 then stree9LRRLRLLL i else stree9LRRLRLLR (i - 15)

def stree9LRRLRLRLL (i : Nat) : State := match i with | 0 => state9_1669 | 1 => state9_1670 | 2 => state9_1671 | 3 => state9_1672 | 4 => state9_1673 | 5 => state9_1674 | 6 => state9_1675 | _ => state9_1676

def stree9LRRLRLRLR (i : Nat) : State := match i with | 0 => state9_1677 | 1 => state9_1678 | 2 => state9_1679 | 3 => state9_1680 | 4 => state9_1681 | 5 => state9_1682 | 6 => state9_1683 | _ => state9_1684

def stree9LRRLRLRL (i : Nat) : State := if i < 8 then stree9LRRLRLRLL i else stree9LRRLRLRLR (i - 8)

def stree9LRRLRLRRL (i : Nat) : State := match i with | 0 => state9_1685 | 1 => state9_1686 | 2 => state9_1687 | 3 => state9_1688 | 4 => state9_1689 | 5 => state9_1690 | 6 => state9_1691 | _ => state9_1692

def stree9LRRLRLRRR (i : Nat) : State := match i with | 0 => state9_1693 | 1 => state9_1694 | 2 => state9_1695 | 3 => state9_1696 | 4 => state9_1697 | 5 => state9_1698 | 6 => state9_1699 | _ => state9_1700

def stree9LRRLRLRR (i : Nat) : State := if i < 8 then stree9LRRLRLRRL i else stree9LRRLRLRRR (i - 8)

def stree9LRRLRLR (i : Nat) : State := if i < 16 then stree9LRRLRLRL i else stree9LRRLRLRR (i - 16)

def stree9LRRLRL (i : Nat) : State := if i < 31 then stree9LRRLRLL i else stree9LRRLRLR (i - 31)

def stree9LRRLRRLLL (i : Nat) : State := match i with | 0 => state9_1701 | 1 => state9_1702 | 2 => state9_1703 | 3 => state9_1704 | 4 => state9_1705 | 5 => state9_1706 | _ => state9_1707

def stree9LRRLRRLLR (i : Nat) : State := match i with | 0 => state9_1708 | 1 => state9_1709 | 2 => state9_1710 | 3 => state9_1711 | 4 => state9_1712 | 5 => state9_1713 | 6 => state9_1714 | _ => state9_1715

def stree9LRRLRRLL (i : Nat) : State := if i < 7 then stree9LRRLRRLLL i else stree9LRRLRRLLR (i - 7)

def stree9LRRLRRLRL (i : Nat) : State := match i with | 0 => state9_1716 | 1 => state9_1717 | 2 => state9_1718 | 3 => state9_1719 | 4 => state9_1720 | 5 => state9_1721 | 6 => state9_1722 | _ => state9_1723

def stree9LRRLRRLRR (i : Nat) : State := match i with | 0 => state9_1724 | 1 => state9_1725 | 2 => state9_1726 | 3 => state9_1727 | 4 => state9_1728 | 5 => state9_1729 | 6 => state9_1730 | _ => state9_1731

def stree9LRRLRRLR (i : Nat) : State := if i < 8 then stree9LRRLRRLRL i else stree9LRRLRRLRR (i - 8)

def stree9LRRLRRL (i : Nat) : State := if i < 15 then stree9LRRLRRLL i else stree9LRRLRRLR (i - 15)

def stree9LRRLRRRLL (i : Nat) : State := match i with | 0 => state9_1732 | 1 => state9_1733 | 2 => state9_1734 | 3 => state9_1735 | 4 => state9_1736 | 5 => state9_1737 | 6 => state9_1738 | _ => state9_1739

def stree9LRRLRRRLR (i : Nat) : State := match i with | 0 => state9_1740 | 1 => state9_1741 | 2 => state9_1742 | 3 => state9_1743 | 4 => state9_1744 | 5 => state9_1745 | 6 => state9_1746 | _ => state9_1747

def stree9LRRLRRRL (i : Nat) : State := if i < 8 then stree9LRRLRRRLL i else stree9LRRLRRRLR (i - 8)

def stree9LRRLRRRRL (i : Nat) : State := match i with | 0 => state9_1748 | 1 => state9_1749 | 2 => state9_1750 | 3 => state9_1751 | 4 => state9_1752 | 5 => state9_1753 | 6 => state9_1754 | _ => state9_1755

def stree9LRRLRRRRR (i : Nat) : State := match i with | 0 => state9_1756 | 1 => state9_1757 | 2 => state9_1758 | 3 => state9_1759 | 4 => state9_1760 | 5 => state9_1761 | 6 => state9_1762 | _ => state9_1763

def stree9LRRLRRRR (i : Nat) : State := if i < 8 then stree9LRRLRRRRL i else stree9LRRLRRRRR (i - 8)

def stree9LRRLRRR (i : Nat) : State := if i < 16 then stree9LRRLRRRL i else stree9LRRLRRRR (i - 16)

def stree9LRRLRR (i : Nat) : State := if i < 31 then stree9LRRLRRL i else stree9LRRLRRR (i - 31)

def stree9LRRLR (i : Nat) : State := if i < 63 then stree9LRRLRL i else stree9LRRLRR (i - 63)

def stree9LRRL (i : Nat) : State := if i < 126 then stree9LRRLL i else stree9LRRLR (i - 126)

def stree9LRRRLLLLL (i : Nat) : State := match i with | 0 => state9_1764 | 1 => state9_1765 | 2 => state9_1766 | 3 => state9_1767 | 4 => state9_1768 | 5 => state9_1769 | _ => state9_1770

def stree9LRRRLLLLR (i : Nat) : State := match i with | 0 => state9_1771 | 1 => state9_1772 | 2 => state9_1773 | 3 => state9_1774 | 4 => state9_1775 | 5 => state9_1776 | 6 => state9_1777 | _ => state9_1778

def stree9LRRRLLLL (i : Nat) : State := if i < 7 then stree9LRRRLLLLL i else stree9LRRRLLLLR (i - 7)

def stree9LRRRLLLRL (i : Nat) : State := match i with | 0 => state9_1779 | 1 => state9_1780 | 2 => state9_1781 | 3 => state9_1782 | 4 => state9_1783 | 5 => state9_1784 | 6 => state9_1785 | _ => state9_1786

def stree9LRRRLLLRR (i : Nat) : State := match i with | 0 => state9_1787 | 1 => state9_1788 | 2 => state9_1789 | 3 => state9_1790 | 4 => state9_1791 | 5 => state9_1792 | 6 => state9_1793 | _ => state9_1794

def stree9LRRRLLLR (i : Nat) : State := if i < 8 then stree9LRRRLLLRL i else stree9LRRRLLLRR (i - 8)

def stree9LRRRLLL (i : Nat) : State := if i < 15 then stree9LRRRLLLL i else stree9LRRRLLLR (i - 15)

def stree9LRRRLLRLL (i : Nat) : State := match i with | 0 => state9_1795 | 1 => state9_1796 | 2 => state9_1797 | 3 => state9_1798 | 4 => state9_1799 | 5 => state9_1800 | 6 => state9_1801 | _ => state9_1802

def stree9LRRRLLRLR (i : Nat) : State := match i with | 0 => state9_1803 | 1 => state9_1804 | 2 => state9_1805 | 3 => state9_1806 | 4 => state9_1807 | 5 => state9_1808 | 6 => state9_1809 | _ => state9_1810

def stree9LRRRLLRL (i : Nat) : State := if i < 8 then stree9LRRRLLRLL i else stree9LRRRLLRLR (i - 8)

def stree9LRRRLLRRL (i : Nat) : State := match i with | 0 => state9_1811 | 1 => state9_1812 | 2 => state9_1813 | 3 => state9_1814 | 4 => state9_1815 | 5 => state9_1816 | 6 => state9_1817 | _ => state9_1818

def stree9LRRRLLRRR (i : Nat) : State := match i with | 0 => state9_1819 | 1 => state9_1820 | 2 => state9_1821 | 3 => state9_1822 | 4 => state9_1823 | 5 => state9_1824 | 6 => state9_1825 | _ => state9_1826

def stree9LRRRLLRR (i : Nat) : State := if i < 8 then stree9LRRRLLRRL i else stree9LRRRLLRRR (i - 8)

def stree9LRRRLLR (i : Nat) : State := if i < 16 then stree9LRRRLLRL i else stree9LRRRLLRR (i - 16)

def stree9LRRRLL (i : Nat) : State := if i < 31 then stree9LRRRLLL i else stree9LRRRLLR (i - 31)

def stree9LRRRLRLLL (i : Nat) : State := match i with | 0 => state9_1827 | 1 => state9_1828 | 2 => state9_1829 | 3 => state9_1830 | 4 => state9_1831 | 5 => state9_1832 | _ => state9_1833

def stree9LRRRLRLLR (i : Nat) : State := match i with | 0 => state9_1834 | 1 => state9_1835 | 2 => state9_1836 | 3 => state9_1837 | 4 => state9_1838 | 5 => state9_1839 | 6 => state9_1840 | _ => state9_1841

def stree9LRRRLRLL (i : Nat) : State := if i < 7 then stree9LRRRLRLLL i else stree9LRRRLRLLR (i - 7)

def stree9LRRRLRLRL (i : Nat) : State := match i with | 0 => state9_1842 | 1 => state9_1843 | 2 => state9_1844 | 3 => state9_1845 | 4 => state9_1846 | 5 => state9_1847 | 6 => state9_1848 | _ => state9_1849

def stree9LRRRLRLRR (i : Nat) : State := match i with | 0 => state9_1850 | 1 => state9_1851 | 2 => state9_1852 | 3 => state9_1853 | 4 => state9_1854 | 5 => state9_1855 | 6 => state9_1856 | _ => state9_1857

def stree9LRRRLRLR (i : Nat) : State := if i < 8 then stree9LRRRLRLRL i else stree9LRRRLRLRR (i - 8)

def stree9LRRRLRL (i : Nat) : State := if i < 15 then stree9LRRRLRLL i else stree9LRRRLRLR (i - 15)

def stree9LRRRLRRLL (i : Nat) : State := match i with | 0 => state9_1858 | 1 => state9_1859 | 2 => state9_1860 | 3 => state9_1861 | 4 => state9_1862 | 5 => state9_1863 | 6 => state9_1864 | _ => state9_1865

def stree9LRRRLRRLR (i : Nat) : State := match i with | 0 => state9_1866 | 1 => state9_1867 | 2 => state9_1868 | 3 => state9_1869 | 4 => state9_1870 | 5 => state9_1871 | 6 => state9_1872 | _ => state9_1873

def stree9LRRRLRRL (i : Nat) : State := if i < 8 then stree9LRRRLRRLL i else stree9LRRRLRRLR (i - 8)

def stree9LRRRLRRRL (i : Nat) : State := match i with | 0 => state9_1874 | 1 => state9_1875 | 2 => state9_1876 | 3 => state9_1877 | 4 => state9_1878 | 5 => state9_1879 | 6 => state9_1880 | _ => state9_1881

def stree9LRRRLRRRR (i : Nat) : State := match i with | 0 => state9_1882 | 1 => state9_1883 | 2 => state9_1884 | 3 => state9_1885 | 4 => state9_1886 | 5 => state9_1887 | 6 => state9_1888 | _ => state9_1889

def stree9LRRRLRRR (i : Nat) : State := if i < 8 then stree9LRRRLRRRL i else stree9LRRRLRRRR (i - 8)

def stree9LRRRLRR (i : Nat) : State := if i < 16 then stree9LRRRLRRL i else stree9LRRRLRRR (i - 16)

def stree9LRRRLR (i : Nat) : State := if i < 31 then stree9LRRRLRL i else stree9LRRRLRR (i - 31)

def stree9LRRRL (i : Nat) : State := if i < 63 then stree9LRRRLL i else stree9LRRRLR (i - 63)

def stree9LRRRRLLLL (i : Nat) : State := match i with | 0 => state9_1890 | 1 => state9_1891 | 2 => state9_1892 | 3 => state9_1893 | 4 => state9_1894 | 5 => state9_1895 | _ => state9_1896

def stree9LRRRRLLLR (i : Nat) : State := match i with | 0 => state9_1897 | 1 => state9_1898 | 2 => state9_1899 | 3 => state9_1900 | 4 => state9_1901 | 5 => state9_1902 | 6 => state9_1903 | _ => state9_1904

def stree9LRRRRLLL (i : Nat) : State := if i < 7 then stree9LRRRRLLLL i else stree9LRRRRLLLR (i - 7)

def stree9LRRRRLLRL (i : Nat) : State := match i with | 0 => state9_1905 | 1 => state9_1906 | 2 => state9_1907 | 3 => state9_1908 | 4 => state9_1909 | 5 => state9_1910 | 6 => state9_1911 | _ => state9_1912

def stree9LRRRRLLRR (i : Nat) : State := match i with | 0 => state9_1913 | 1 => state9_1914 | 2 => state9_1915 | 3 => state9_1916 | 4 => state9_1917 | 5 => state9_1918 | 6 => state9_1919 | _ => state9_1920

def stree9LRRRRLLR (i : Nat) : State := if i < 8 then stree9LRRRRLLRL i else stree9LRRRRLLRR (i - 8)

def stree9LRRRRLL (i : Nat) : State := if i < 15 then stree9LRRRRLLL i else stree9LRRRRLLR (i - 15)

def stree9LRRRRLRLL (i : Nat) : State := match i with | 0 => state9_1921 | 1 => state9_1922 | 2 => state9_1923 | 3 => state9_1924 | 4 => state9_1925 | 5 => state9_1926 | 6 => state9_1927 | _ => state9_1928

def stree9LRRRRLRLR (i : Nat) : State := match i with | 0 => state9_1929 | 1 => state9_1930 | 2 => state9_1931 | 3 => state9_1932 | 4 => state9_1933 | 5 => state9_1934 | 6 => state9_1935 | _ => state9_1936

def stree9LRRRRLRL (i : Nat) : State := if i < 8 then stree9LRRRRLRLL i else stree9LRRRRLRLR (i - 8)

def stree9LRRRRLRRL (i : Nat) : State := match i with | 0 => state9_1937 | 1 => state9_1938 | 2 => state9_1939 | 3 => state9_1940 | 4 => state9_1941 | 5 => state9_1942 | 6 => state9_1943 | _ => state9_1944

def stree9LRRRRLRRR (i : Nat) : State := match i with | 0 => state9_1945 | 1 => state9_1946 | 2 => state9_1947 | 3 => state9_1948 | 4 => state9_1949 | 5 => state9_1950 | 6 => state9_1951 | _ => state9_1952

def stree9LRRRRLRR (i : Nat) : State := if i < 8 then stree9LRRRRLRRL i else stree9LRRRRLRRR (i - 8)

def stree9LRRRRLR (i : Nat) : State := if i < 16 then stree9LRRRRLRL i else stree9LRRRRLRR (i - 16)

def stree9LRRRRL (i : Nat) : State := if i < 31 then stree9LRRRRLL i else stree9LRRRRLR (i - 31)

def stree9LRRRRRLLL (i : Nat) : State := match i with | 0 => state9_1953 | 1 => state9_1954 | 2 => state9_1955 | 3 => state9_1956 | 4 => state9_1957 | 5 => state9_1958 | _ => state9_1959

def stree9LRRRRRLLR (i : Nat) : State := match i with | 0 => state9_1960 | 1 => state9_1961 | 2 => state9_1962 | 3 => state9_1963 | 4 => state9_1964 | 5 => state9_1965 | 6 => state9_1966 | _ => state9_1967

def stree9LRRRRRLL (i : Nat) : State := if i < 7 then stree9LRRRRRLLL i else stree9LRRRRRLLR (i - 7)

def stree9LRRRRRLRL (i : Nat) : State := match i with | 0 => state9_1968 | 1 => state9_1969 | 2 => state9_1970 | 3 => state9_1971 | 4 => state9_1972 | 5 => state9_1973 | 6 => state9_1974 | _ => state9_1975

def stree9LRRRRRLRR (i : Nat) : State := match i with | 0 => state9_1976 | 1 => state9_1977 | 2 => state9_1978 | 3 => state9_1979 | 4 => state9_1980 | 5 => state9_1981 | 6 => state9_1982 | _ => state9_1983

def stree9LRRRRRLR (i : Nat) : State := if i < 8 then stree9LRRRRRLRL i else stree9LRRRRRLRR (i - 8)

def stree9LRRRRRL (i : Nat) : State := if i < 15 then stree9LRRRRRLL i else stree9LRRRRRLR (i - 15)

def stree9LRRRRRRLL (i : Nat) : State := match i with | 0 => state9_1984 | 1 => state9_1985 | 2 => state9_1986 | 3 => state9_1987 | 4 => state9_1988 | 5 => state9_1989 | 6 => state9_1990 | _ => state9_1991

def stree9LRRRRRRLR (i : Nat) : State := match i with | 0 => state9_1992 | 1 => state9_1993 | 2 => state9_1994 | 3 => state9_1995 | 4 => state9_1996 | 5 => state9_1997 | 6 => state9_1998 | _ => state9_1999

def stree9LRRRRRRL (i : Nat) : State := if i < 8 then stree9LRRRRRRLL i else stree9LRRRRRRLR (i - 8)

def stree9LRRRRRRRL (i : Nat) : State := match i with | 0 => state9_2000 | 1 => state9_2001 | 2 => state9_2002 | 3 => state9_2003 | 4 => state9_2004 | 5 => state9_2005 | 6 => state9_2006 | _ => state9_2007

def stree9LRRRRRRRR (i : Nat) : State := match i with | 0 => state9_2008 | 1 => state9_2009 | 2 => state9_2010 | 3 => state9_2011 | 4 => state9_2012 | 5 => state9_2013 | 6 => state9_2014 | _ => state9_2015

def stree9LRRRRRRR (i : Nat) : State := if i < 8 then stree9LRRRRRRRL i else stree9LRRRRRRRR (i - 8)

def stree9LRRRRRR (i : Nat) : State := if i < 16 then stree9LRRRRRRL i else stree9LRRRRRRR (i - 16)

def stree9LRRRRR (i : Nat) : State := if i < 31 then stree9LRRRRRL i else stree9LRRRRRR (i - 31)

def stree9LRRRR (i : Nat) : State := if i < 63 then stree9LRRRRL i else stree9LRRRRR (i - 63)

def stree9LRRR (i : Nat) : State := if i < 126 then stree9LRRRL i else stree9LRRRR (i - 126)

def stree9LRR (i : Nat) : State := if i < 252 then stree9LRRL i else stree9LRRR (i - 252)

def stree9LR (i : Nat) : State := if i < 504 then stree9LRL i else stree9LRR (i - 504)

def stree9L (i : Nat) : State := if i < 1008 then stree9LL i else stree9LR (i - 1008)

def stree9RLLLLLLLL (i : Nat) : State := match i with | 0 => state9_2016 | 1 => state9_2017 | 2 => state9_2018 | 3 => state9_2019 | 4 => state9_2020 | 5 => state9_2021 | _ => state9_2022

def stree9RLLLLLLLR (i : Nat) : State := match i with | 0 => state9_2023 | 1 => state9_2024 | 2 => state9_2025 | 3 => state9_2026 | 4 => state9_2027 | 5 => state9_2028 | 6 => state9_2029 | _ => state9_2030

def stree9RLLLLLLL (i : Nat) : State := if i < 7 then stree9RLLLLLLLL i else stree9RLLLLLLLR (i - 7)

def stree9RLLLLLLRL (i : Nat) : State := match i with | 0 => state9_2031 | 1 => state9_2032 | 2 => state9_2033 | 3 => state9_2034 | 4 => state9_2035 | 5 => state9_2036 | 6 => state9_2037 | _ => state9_2038

def stree9RLLLLLLRR (i : Nat) : State := match i with | 0 => state9_2039 | 1 => state9_2040 | 2 => state9_2041 | 3 => state9_2042 | 4 => state9_2043 | 5 => state9_2044 | 6 => state9_2045 | _ => state9_2046

def stree9RLLLLLLR (i : Nat) : State := if i < 8 then stree9RLLLLLLRL i else stree9RLLLLLLRR (i - 8)

def stree9RLLLLLL (i : Nat) : State := if i < 15 then stree9RLLLLLLL i else stree9RLLLLLLR (i - 15)

def stree9RLLLLLRLL (i : Nat) : State := match i with | 0 => state9_2047 | 1 => state9_2048 | 2 => state9_2049 | 3 => state9_2050 | 4 => state9_2051 | 5 => state9_2052 | 6 => state9_2053 | _ => state9_2054

def stree9RLLLLLRLR (i : Nat) : State := match i with | 0 => state9_2055 | 1 => state9_2056 | 2 => state9_2057 | 3 => state9_2058 | 4 => state9_2059 | 5 => state9_2060 | 6 => state9_2061 | _ => state9_2062

def stree9RLLLLLRL (i : Nat) : State := if i < 8 then stree9RLLLLLRLL i else stree9RLLLLLRLR (i - 8)

def stree9RLLLLLRRL (i : Nat) : State := match i with | 0 => state9_2063 | 1 => state9_2064 | 2 => state9_2065 | 3 => state9_2066 | 4 => state9_2067 | 5 => state9_2068 | 6 => state9_2069 | _ => state9_2070

def stree9RLLLLLRRR (i : Nat) : State := match i with | 0 => state9_2071 | 1 => state9_2072 | 2 => state9_2073 | 3 => state9_2074 | 4 => state9_2075 | 5 => state9_2076 | 6 => state9_2077 | _ => state9_2078

def stree9RLLLLLRR (i : Nat) : State := if i < 8 then stree9RLLLLLRRL i else stree9RLLLLLRRR (i - 8)

def stree9RLLLLLR (i : Nat) : State := if i < 16 then stree9RLLLLLRL i else stree9RLLLLLRR (i - 16)

def stree9RLLLLL (i : Nat) : State := if i < 31 then stree9RLLLLLL i else stree9RLLLLLR (i - 31)

def stree9RLLLLRLLL (i : Nat) : State := match i with | 0 => state9_2079 | 1 => state9_2080 | 2 => state9_2081 | 3 => state9_2082 | 4 => state9_2083 | 5 => state9_2084 | _ => state9_2085

def stree9RLLLLRLLR (i : Nat) : State := match i with | 0 => state9_2086 | 1 => state9_2087 | 2 => state9_2088 | 3 => state9_2089 | 4 => state9_2090 | 5 => state9_2091 | 6 => state9_2092 | _ => state9_2093

def stree9RLLLLRLL (i : Nat) : State := if i < 7 then stree9RLLLLRLLL i else stree9RLLLLRLLR (i - 7)

def stree9RLLLLRLRL (i : Nat) : State := match i with | 0 => state9_2094 | 1 => state9_2095 | 2 => state9_2096 | 3 => state9_2097 | 4 => state9_2098 | 5 => state9_2099 | 6 => state9_2100 | _ => state9_2101

def stree9RLLLLRLRR (i : Nat) : State := match i with | 0 => state9_2102 | 1 => state9_2103 | 2 => state9_2104 | 3 => state9_2105 | 4 => state9_2106 | 5 => state9_2107 | 6 => state9_2108 | _ => state9_2109

def stree9RLLLLRLR (i : Nat) : State := if i < 8 then stree9RLLLLRLRL i else stree9RLLLLRLRR (i - 8)

def stree9RLLLLRL (i : Nat) : State := if i < 15 then stree9RLLLLRLL i else stree9RLLLLRLR (i - 15)

def stree9RLLLLRRLL (i : Nat) : State := match i with | 0 => state9_2110 | 1 => state9_2111 | 2 => state9_2112 | 3 => state9_2113 | 4 => state9_2114 | 5 => state9_2115 | 6 => state9_2116 | _ => state9_2117

def stree9RLLLLRRLR (i : Nat) : State := match i with | 0 => state9_2118 | 1 => state9_2119 | 2 => state9_2120 | 3 => state9_2121 | 4 => state9_2122 | 5 => state9_2123 | 6 => state9_2124 | _ => state9_2125

def stree9RLLLLRRL (i : Nat) : State := if i < 8 then stree9RLLLLRRLL i else stree9RLLLLRRLR (i - 8)

def stree9RLLLLRRRL (i : Nat) : State := match i with | 0 => state9_2126 | 1 => state9_2127 | 2 => state9_2128 | 3 => state9_2129 | 4 => state9_2130 | 5 => state9_2131 | 6 => state9_2132 | _ => state9_2133

def stree9RLLLLRRRR (i : Nat) : State := match i with | 0 => state9_2134 | 1 => state9_2135 | 2 => state9_2136 | 3 => state9_2137 | 4 => state9_2138 | 5 => state9_2139 | 6 => state9_2140 | _ => state9_2141

def stree9RLLLLRRR (i : Nat) : State := if i < 8 then stree9RLLLLRRRL i else stree9RLLLLRRRR (i - 8)

def stree9RLLLLRR (i : Nat) : State := if i < 16 then stree9RLLLLRRL i else stree9RLLLLRRR (i - 16)

def stree9RLLLLR (i : Nat) : State := if i < 31 then stree9RLLLLRL i else stree9RLLLLRR (i - 31)

def stree9RLLLL (i : Nat) : State := if i < 63 then stree9RLLLLL i else stree9RLLLLR (i - 63)

def stree9RLLLRLLLL (i : Nat) : State := match i with | 0 => state9_2142 | 1 => state9_2143 | 2 => state9_2144 | 3 => state9_2145 | 4 => state9_2146 | 5 => state9_2147 | _ => state9_2148

def stree9RLLLRLLLR (i : Nat) : State := match i with | 0 => state9_2149 | 1 => state9_2150 | 2 => state9_2151 | 3 => state9_2152 | 4 => state9_2153 | 5 => state9_2154 | 6 => state9_2155 | _ => state9_2156

def stree9RLLLRLLL (i : Nat) : State := if i < 7 then stree9RLLLRLLLL i else stree9RLLLRLLLR (i - 7)

def stree9RLLLRLLRL (i : Nat) : State := match i with | 0 => state9_2157 | 1 => state9_2158 | 2 => state9_2159 | 3 => state9_2160 | 4 => state9_2161 | 5 => state9_2162 | 6 => state9_2163 | _ => state9_2164

def stree9RLLLRLLRR (i : Nat) : State := match i with | 0 => state9_2165 | 1 => state9_2166 | 2 => state9_2167 | 3 => state9_2168 | 4 => state9_2169 | 5 => state9_2170 | 6 => state9_2171 | _ => state9_2172

def stree9RLLLRLLR (i : Nat) : State := if i < 8 then stree9RLLLRLLRL i else stree9RLLLRLLRR (i - 8)

def stree9RLLLRLL (i : Nat) : State := if i < 15 then stree9RLLLRLLL i else stree9RLLLRLLR (i - 15)

def stree9RLLLRLRLL (i : Nat) : State := match i with | 0 => state9_2173 | 1 => state9_2174 | 2 => state9_2175 | 3 => state9_2176 | 4 => state9_2177 | 5 => state9_2178 | 6 => state9_2179 | _ => state9_2180

def stree9RLLLRLRLR (i : Nat) : State := match i with | 0 => state9_2181 | 1 => state9_2182 | 2 => state9_2183 | 3 => state9_2184 | 4 => state9_2185 | 5 => state9_2186 | 6 => state9_2187 | _ => state9_2188

def stree9RLLLRLRL (i : Nat) : State := if i < 8 then stree9RLLLRLRLL i else stree9RLLLRLRLR (i - 8)

def stree9RLLLRLRRL (i : Nat) : State := match i with | 0 => state9_2189 | 1 => state9_2190 | 2 => state9_2191 | 3 => state9_2192 | 4 => state9_2193 | 5 => state9_2194 | 6 => state9_2195 | _ => state9_2196

def stree9RLLLRLRRR (i : Nat) : State := match i with | 0 => state9_2197 | 1 => state9_2198 | 2 => state9_2199 | 3 => state9_2200 | 4 => state9_2201 | 5 => state9_2202 | 6 => state9_2203 | _ => state9_2204

def stree9RLLLRLRR (i : Nat) : State := if i < 8 then stree9RLLLRLRRL i else stree9RLLLRLRRR (i - 8)

def stree9RLLLRLR (i : Nat) : State := if i < 16 then stree9RLLLRLRL i else stree9RLLLRLRR (i - 16)

def stree9RLLLRL (i : Nat) : State := if i < 31 then stree9RLLLRLL i else stree9RLLLRLR (i - 31)

def stree9RLLLRRLLL (i : Nat) : State := match i with | 0 => state9_2205 | 1 => state9_2206 | 2 => state9_2207 | 3 => state9_2208 | 4 => state9_2209 | 5 => state9_2210 | _ => state9_2211

def stree9RLLLRRLLR (i : Nat) : State := match i with | 0 => state9_2212 | 1 => state9_2213 | 2 => state9_2214 | 3 => state9_2215 | 4 => state9_2216 | 5 => state9_2217 | 6 => state9_2218 | _ => state9_2219

def stree9RLLLRRLL (i : Nat) : State := if i < 7 then stree9RLLLRRLLL i else stree9RLLLRRLLR (i - 7)

def stree9RLLLRRLRL (i : Nat) : State := match i with | 0 => state9_2220 | 1 => state9_2221 | 2 => state9_2222 | 3 => state9_2223 | 4 => state9_2224 | 5 => state9_2225 | 6 => state9_2226 | _ => state9_2227

def stree9RLLLRRLRR (i : Nat) : State := match i with | 0 => state9_2228 | 1 => state9_2229 | 2 => state9_2230 | 3 => state9_2231 | 4 => state9_2232 | 5 => state9_2233 | 6 => state9_2234 | _ => state9_2235

def stree9RLLLRRLR (i : Nat) : State := if i < 8 then stree9RLLLRRLRL i else stree9RLLLRRLRR (i - 8)

def stree9RLLLRRL (i : Nat) : State := if i < 15 then stree9RLLLRRLL i else stree9RLLLRRLR (i - 15)

def stree9RLLLRRRLL (i : Nat) : State := match i with | 0 => state9_2236 | 1 => state9_2237 | 2 => state9_2238 | 3 => state9_2239 | 4 => state9_2240 | 5 => state9_2241 | 6 => state9_2242 | _ => state9_2243

def stree9RLLLRRRLR (i : Nat) : State := match i with | 0 => state9_2244 | 1 => state9_2245 | 2 => state9_2246 | 3 => state9_2247 | 4 => state9_2248 | 5 => state9_2249 | 6 => state9_2250 | _ => state9_2251

def stree9RLLLRRRL (i : Nat) : State := if i < 8 then stree9RLLLRRRLL i else stree9RLLLRRRLR (i - 8)

def stree9RLLLRRRRL (i : Nat) : State := match i with | 0 => state9_2252 | 1 => state9_2253 | 2 => state9_2254 | 3 => state9_2255 | 4 => state9_2256 | 5 => state9_2257 | 6 => state9_2258 | _ => state9_2259

def stree9RLLLRRRRR (i : Nat) : State := match i with | 0 => state9_2260 | 1 => state9_2261 | 2 => state9_2262 | 3 => state9_2263 | 4 => state9_2264 | 5 => state9_2265 | 6 => state9_2266 | _ => state9_2267

def stree9RLLLRRRR (i : Nat) : State := if i < 8 then stree9RLLLRRRRL i else stree9RLLLRRRRR (i - 8)

def stree9RLLLRRR (i : Nat) : State := if i < 16 then stree9RLLLRRRL i else stree9RLLLRRRR (i - 16)

def stree9RLLLRR (i : Nat) : State := if i < 31 then stree9RLLLRRL i else stree9RLLLRRR (i - 31)

def stree9RLLLR (i : Nat) : State := if i < 63 then stree9RLLLRL i else stree9RLLLRR (i - 63)

def stree9RLLL (i : Nat) : State := if i < 126 then stree9RLLLL i else stree9RLLLR (i - 126)

def stree9RLLRLLLLL (i : Nat) : State := match i with | 0 => state9_2268 | 1 => state9_2269 | 2 => state9_2270 | 3 => state9_2271 | 4 => state9_2272 | 5 => state9_2273 | _ => state9_2274

end Paper2.Certificates.Q6.Coverage
