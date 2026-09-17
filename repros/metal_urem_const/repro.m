// clang -fobjc-arc -framework Metal -framework Foundation repro.m && ./a.out
// The same expression on the CPU and on the GPU, with the divisor 3 coming
// from run time (argc + 2 here, thread id + 3 there). Expected "0" twice;
// Apple's GPU backend gives 2147483525.
#import <Metal/Metal.h>
#define STR_(x) #x
#define STR(x) STR_(x)
int main(int argc, char** argv) {
  unsigned d = argc + 2;
  unsigned o = 4294967295u % d;
  printf("cpu %u\n", o);

  id<MTLDevice> dev = MTLCreateSystemDefaultDevice();
  NSString* src = @""
    "#include <metal_stdlib>\n"
    "kernel void k(device uint* o [[buffer(0)]], uint id [[thread_position_in_grid]]) {"
    "  uint d = id + 3;"
    "  o[0] = 4294967295u % d;"
    "}";
  id<MTLLibrary> lib = [dev newLibraryWithSource:src options:nil error:nil];
  id<MTLComputePipelineState> ps = [dev newComputePipelineStateWithFunction:[lib newFunctionWithName:@"k"] error:nil];
  id<MTLBuffer> out = [dev newBufferWithLength:4 options:MTLResourceStorageModeShared];
  id<MTLCommandBuffer> cb = [[dev newCommandQueue] commandBuffer];
  id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
  [enc setComputePipelineState:ps];
  [enc setBuffer:out offset:0 atIndex:0];
  [enc dispatchThreads:MTLSizeMake(1, 1, 1) threadsPerThreadgroup:MTLSizeMake(1, 1, 1)];
  [enc endEncoding];
  [cb commit];
  [cb waitUntilCompleted];
  printf("gpu %u\n", *(unsigned*)out.contents);

  return 0;
}
