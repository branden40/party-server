/* [RP-V7.148] Halloween photo decor — the spider and bats animated
   loops are REMOVED by Branden's word (Oct 30, 2026: "Take this box
   picture off and Halloween theme let it blend in with the screen").
   The loops were photo animations on pure black meant to screen-blend,
   but iOS WebKit does not blend animated image layers — they painted
   as solid black rectangles over the room scenes. The static
   dew-covered photo webs (inline in the client CSS, screen-blended)
   blend correctly and remain, with the garland and floaters. This
   module now intentionally provides no critter loops. */
window.RP_DECOR_HW = {};
